/*
        gitbrute-rs: vanity git commit id brute forcer implemented in Rust

    Copyright (C) 2020 hspug.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

*/

// The gitbrute command brute-forces a git commit hash prefix.

fn main() -> Result<(), std::io::Error> {
        let matches = clap::App::new("gitbrute-rs").args_from_usage(
                        "--prefix=<deadbeef> 'Desired prefix.'
                        --prefix-bits=[13]    'Number of significant bits in the prefix.'
                        --timezone           'Allow timezone modifications at 15 minutes granularity.'
                        --timezone-minutes   'Allow timezone modifications at minute granularity.'
                        --force              'Re-run, even if current hash matches prefix.'
                        --verbose            'Issue diagnostic messages.'
                        --cpus=[2]           'Number of CPUs to use. Defaults to number of processors.'")
                .get_matches();

        let verbose = matches.is_present("verbose");

        let prefix = matches.value_of("prefix").expect("--prefix arg is mandatory, clap-rs should have already been None-checked it.");
        if prefix.len() > 8 || prefix.chars().any(|c| !"0123456789abcdef".contains(c)) {
                panic!("Invalid prefix.");
        }

        let prefixbits =
                matches.value_of("prefix-bits")
                .map(|s| s.parse().expect(&format!("wrong --prefix-bits value: {}", s)))
                .unwrap_or(prefix.len()*4);

        let prefixbin: Vec<_> = {
                use rustc_hex::FromHex;
                if prefix.len() % 2 == 1 {
                        let mut s = prefix.to_owned();
                        s.push('0');
                        s
                } else {
                        prefix.to_owned()
                }.from_hex().expect(&format!("Invalid hexa prefix: {}", prefix))
        };

        if (prefixbits + 3) / 4 != prefix.len() {
                panic!("--prefix-bits don't correspond to prefix: ({} + 3) / 4 != {}", (prefixbits + 3) / 4, prefix.len());
        }

        let force = matches.is_present("force");
        let timezone = matches.is_present("timezone");
        let timezone_minutes = matches.is_present("timezone-minutes");
        let cpu =
                matches.value_of("cpus")
                .map(|s| s.parse().expect(&format!("wrong cpus value: {}", s)))
                .unwrap_or(num_cpus::get());

        if !force {
                let hash: Vec<u8> = {use rustc_hex::FromHex; cur_hash()?.from_hex().map_err(|e| errmap("HEAD hash parse", &e))?};
                let mask = make_mask(prefixbits);
                if matches_with_mask(&hash, &prefixbin, &mask) {
                        return Ok(());
                }
        }

        let obj = std::process::Command::new("git").args(&["cat-file", "-p", "HEAD"]).output()?;
        if !obj.status.success() {
                panic!("Failed to load git object.");
        }

        let obj = obj.stdout;

        let done = (std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)), std::sync::Arc::new(std::sync::atomic::AtomicI32::new(0)));

        let (possibilities_tx, possibilities_rx) = spmc::channel();
        let feeder = {
                let done = done.clone();
                std::thread::spawn(move || {
                        possibilities(possibilities_tx, timezone, timezone_minutes, force, done);
                })
        };

        let (winner_rx, forcers) = { // ensure winner_tx is dropped
                let (winner_tx, winner_rx) = std::sync::mpsc::channel();
                let mut forcers = Vec::new();
                for _i in 0..cpu {
                        let tx = winner_tx.clone();
                        let rx = possibilities_rx.clone();
                        let or = obj.clone();
                        let pr = prefixbin.clone();
                        let done = done.clone();
                        forcers.push(std::thread::spawn(move || {
                                brute_force(or, tx, rx, pr, prefixbits, done)
                        }));
                }
                (winner_rx, forcers)
        };

        let w = winner_rx.recv().map_err(|e| errmap("winner recv failed: ", &e))?;
        if verbose {
                println!("{:?}", w);
        }
        done.0.store(true, std::sync::atomic::Ordering::SeqCst);
        feeder.join().map_err(|e| errmap("feeder join", &format!("{:?}", e)))?;
        for f in forcers.into_iter() {
                f.join().map_err(|e| errmap("forcer join", &format!("{:?}", e)))?;
        }

        let cmd =
                std::process::Command::new("git").args(&["commit", "--allow-empty", "--amend", &format!("--date={}", w.author), "--reuse-message=HEAD"])
                .env("GIT_COMMITTER_DATE", w.committer)
                .output()?;

        if !cmd.status.success() {
                Err(errmap("", &format!("Failed to amend git object: {}: {:?}", cmd.status, String::from_utf8(cmd.stdout))))
        } else {
                if verbose {
                        println!("new hash: {}", cur_hash()?);
                }
                Ok(())
        }
}

fn make_mask(bits: usize) -> Vec<u8> {
        (0..bits/8).map(|_| 0xffu8)
        .chain(
                if bits % 8 != 0 {
                        vec![0xffu8 << (8 - bits % 8)].into_iter()
                } else {
                        vec![].into_iter()
                })
        .collect()
}

fn matches_with_mask(v1: &[u8], v2: &[u8], mask: &[u8]) -> bool {
        v1.iter().zip(v2.iter()).zip(mask.iter()).all(|((h, p), m)| (*h&*m)^(*p&*m) == 0)
}

fn cur_hash() -> Result<String, std::io::Error> {
        let cmd =
                std::process::Command::new("git").args(&["rev-parse", "HEAD"])
                .output()?;
        if !cmd.status.success() {
                panic!("Failed to get HEAD hash.");
        }
        Ok(String::from_utf8(cmd.stdout).map_err(|e| errmap("", &e))?.trim().to_owned())
}

fn possibilities(mut possibilities_tx: spmc::Sender<Possibility>, timezone: bool, timezone_minutes: bool, force: bool, done: (std::sync::Arc<std::sync::atomic::AtomicBool>, std::sync::Arc<std::sync::atomic::AtomicI32>)) {
        let mut generated = 0;
        let tzpossibilities: Vec<i32> =
                if timezone_minutes {
                        (1..12*60*2) // every minute for both hemispheres, but including 0 only once
                                .into_iter()
                                .map(|t| if t % 2 == 0 { 1 } else { -1 } * (t / 2))
                                .collect()
                } else if timezone {
                        (1..12*4*2) // every 15 minutes for both hemispheres, but including 0 only once
                                .into_iter()
                                .map(|t| if t % 2 == 0 { 1 } else  { -1 } * (t / 2))
                                .map(|t| t * 15)
                                .collect()
                } else {
                        vec![0] // don't touch the timezone
                };

        let mut possibilities = std::collections::VecDeque::new();
        possibilities.push_back((0i32, if force { 1i32 } else { 0i32 }));

        'main:
        while let Some((ad, cd)) = possibilities.pop_front() {
                for atz in tzpossibilities.iter() {
                        for ctz in tzpossibilities.iter() {
                                let ao = Offset{time_offset: ad, timezone_offset: *atz};
                                let co = Offset{time_offset: cd, timezone_offset: *ctz};
                                let next_possibility = Possibility{serial: generated, author: ao, committer: co};
                                if possibilities_tx.send(next_possibility).is_err() || done.0.load(std::sync::atomic::Ordering::SeqCst) {
                                        break 'main;
                                } else {
                                        generated += 1;
                                        let val = done.1.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                        if  val > 10000 {
                                                std::thread::sleep(std::time::Duration::from_millis(val as u64 / 10000));
                                                //println!("Overload! {}", val);
                                        }
                                }
                        }
                }
                if ad == 0 && cd == 0 || ad >= 0 && cd > 0  || ad > 0 && cd >= 0 {
                        // only generate new values for the "main" path, that is the non-negative pairs
                        fn pm(i: i32) -> Vec<i32> {
                                vec![i, -i]
                        }
                        let (ad, cd) =
                                if ad + 1 < cd {
                                        (pm(ad + 1), pm(cd))
                                } else if cd + 1 < ad {
                                        (pm(ad), pm(cd + 1))
                                } else if ad < cd {
                                        (pm(ad + 1), vec![0])
                                } else if ad == cd {
                                        (vec![0], pm(cd + 1))
                                } else {
                                        assert!(ad == cd + 1);
                                        (pm(ad), pm(cd + 1))
                                };
                        for ad in ad.iter() {
                                for cd in cd.iter() {
                                        possibilities.push_back((*ad, *cd));
                                }
                        }
                        if possibilities.len() > 100 {
                                println!("queue length: {}", possibilities.len());
                        }
                }
        }
}

#[derive(Debug)]
struct Solution {
        generated: u64,
        author: String,
        committer: String,
}
#[derive(Debug)]
struct Offset {
        time_offset: i32,
        timezone_offset: i32,
}
#[derive(Debug)]
struct Possibility {
        serial: u64,
        author: Offset,
        committer: Offset,
}

fn brute_force(obj: Vec<u8>, winner_tx: std::sync::mpsc::Sender<Solution>, possibilities_rx: spmc::Receiver<Possibility>, prefixbin: Vec<u8>, prefixbits: usize, done: (std::sync::Arc<std::sync::atomic::AtomicBool>, std::sync::Arc<std::sync::atomic::AtomicI32>)) -> () {
        let (before_author_date, author_date, between_dates, committer_date, after_committer_date) = parse_obj(&obj).expect("invalid git object description");

        let mut intro = format!("commit {}\0", obj.len()).as_bytes().to_owned();

        let mut adatei = intro.len() + before_author_date.len();
        let mut cdatei = adatei + author_date.len() + between_dates.len();

        // blob is the blob to mutate in-place repatedly while testing
        // whether we have a match.
        let mut blob = Vec::new();
        for s in vec![&intro as &[u8], before_author_date, author_date, between_dates, committer_date, after_committer_date] {
                blob.extend_from_slice(s);
        }

        fn parse_date(s: &[u8]) -> (i64, i32) {
                let mut v = 0i64;
                for b in s.iter() {
                        if *b == b' ' {
                                break;
                        }
                        v = 10*v + *b as i64 - b'0' as i64;
                }

                let mut tz: i32 = 0;
                tz += (s[s.len() - 1] - b'0') as i32;
                tz += 10*(s[s.len() - 2] - b'0') as i32;
                tz += 60*(s[s.len() - 3] - b'0') as i32;
                tz += 600*(s[s.len() - 4] - b'0') as i32;
                tz *= if s[s.len() - 5] == b'-' { -1 } else { 1 };

                (v, tz)
        };

        let (ad_base, adtz_base) = parse_date(author_date);
        let mut adlen = author_date.len();
        let (cd_base, cdtz_base) = parse_date(committer_date);
        let mut cdlen = committer_date.len();

        fn tzformat(base_mins: i32, offset: i32) -> String {
                let mut res = base_mins + offset;
                if res < -12*60 {
                        res = 12*60 + (res + 12*60);
                } else if res > 12*60 {
                        res = -12*60 + (res - 12*60); 
                }
                let pres = res.abs();
                format!("{}{:0>2}{:0>2}", if res < 0 { '-' } else { '+' }, pres / 60, pres % 60)
        }

        let mut s1 = crypto::sha1::Sha1::new();
        let mask: Vec<u8> = make_mask(prefixbits);

        fn splice(dst: &mut [u8], offset: usize, src: &[u8]) {
                for (d, s) in dst.iter_mut().skip(offset).zip(src.iter()) {
                        *d = *s;
                }
        }

        //fn dump(tag: &str, b: &[u8]) { println!("{}: >{}<", tag, std::str::from_utf8(b).unwrap()); }
        while let Ok(p) = possibilities_rx.recv() {
                done.1.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                //println!("trying {:?}", p);
                if ad_base + (p.author.time_offset as i64) < 0 || cd_base + (p.committer.time_offset as i64) < 0 {
                        continue;
                }
                let ads = format!("@{} {}", ad_base + p.author.time_offset as i64, tzformat(adtz_base, p.author.timezone_offset));
                let ad = &ads.as_bytes()[1..];
                let cds = format!("@{} {}", cd_base + p.committer.time_offset as i64, tzformat(cdtz_base, p.committer.timezone_offset));
                let cd = &cds.as_bytes()[1..];

                if ad.len() == adlen && cd.len() == cdlen {
                        splice(&mut blob, cdatei, cd);
                        splice(&mut blob, adatei, ad);
                } else {
                        //dump("extending blob", &blob);

                        let objlen: usize = vec![before_author_date, ad, between_dates, cd, after_committer_date].into_iter().map(|s| s.len()).sum();
                        intro = format!("commit {}\0", objlen).as_bytes().to_owned();

                        blob = Vec::with_capacity(objlen + intro.len());
                        for s in vec![&intro as &[u8], before_author_date, ad, between_dates, cd, after_committer_date] {
                                blob.extend_from_slice(s);
                        }

                        adlen = ad.len();
                        cdlen = cd.len();

                        adatei = intro.len() + before_author_date.len();
                        cdatei = adatei + ad.len() + between_dates.len();

                        //dump("extended blob", &blob);
                }

                let mut hash = vec![0u8; 20];
                {
                        use crypto::digest::Digest;
                        s1.reset();
                        //println!("hashing: {}", std::str::from_utf8(&blob).unwrap());
                        s1.input(&blob);
                        s1.result(&mut hash);
                }

                if done.0.load(std::sync::atomic::Ordering::SeqCst) {
                        break;
                }

                if matches_with_mask(&hash, &prefixbin, &mask) {
                        let winner = Solution{generated: p.serial, author: ads, committer: cds};
                        //println!("winner found: {:?}", winner);
                        winner_tx.send(winner).expect("failed to send result");
                        break;
                } else {
                        //{use rustc_hex::ToHex;println!("wrong hash: {} serial {}", hash.to_hex::<String>(), p.serial);}
                }
        }
        //println!("No more possibilities.");
}

fn parse_obj(obj: &[u8]) -> Result<(&[u8], &[u8], &[u8], &[u8], &[u8]), ()> {
        fn date<'a>(i: &mut impl Iterator<Item=(usize, &'a u8)>) -> Result<(usize, usize), ()> {
                let mut date = 0;
                let mut tz = 0;
                let mut eol = 0;
                let mut spc = false;
                let mut nl = false;
                while let Some((idx, _)) = i.find(|b| {spc = b.1 == &b' '; spc} || {nl = b.1 == &b'\n'; nl}) {
                        if spc {
                                date = tz;
                                tz = idx + 1;
                        } else if nl {
                                eol = idx;
                                break;
                        }
                }
                if date > 0 && eol > 0 {
                        Ok((date, eol))
                } else {
                        Err(())
                }
        }
        let mut i = obj.iter().enumerate();
        while let Some((_, c)) = i.next() {
                if c == &b'a' {
                        break;
                }
                i.position(|b| b.1 == &b'\n').expect("cannot parse object: looking for author line");
        }
        let (author_date_idx, between_dates_idx) = date(&mut i).expect("cannot parse object: author date");
        let (committer_date_idx, after_committer_date_idx) = date(&mut i).expect("cannot parse object: committer date");

        let (before_author_date, tmp) = obj.split_at(author_date_idx);
        let (author_date, tmp) = tmp.split_at(between_dates_idx - author_date_idx);
        let (between_dates, tmp) = tmp.split_at(committer_date_idx - between_dates_idx);
        let (committer_date, after_committer_date) = tmp.split_at(after_committer_date_idx - committer_date_idx);

        Ok((before_author_date, author_date, between_dates, committer_date, after_committer_date))
}

fn errmap<E: std::fmt::Display>(context: &str, e: &E) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{}{}", context, e))
}
