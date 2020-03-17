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
                let hash: Vec<u8> = {use rustc_hex::FromHex; cur_hash(verbose).map_err(|e| errmap("Current hash", &e))?.from_hex().map_err(|e| errmap("HEAD hash parse", &e))?};
                let mask = make_mask(prefixbits);
                if matches_with_mask(&hash, &prefixbin, &mask) {
                        return Ok(());
                }
        }

        let obj = git(verbose, &["cat-file", "-p", "HEAD"]).map_err(|e| errmap("failed to load git object for HEAD", &e))?;

	let mut pi = PossibilityIterator{
			serial: 0,
			possibility_counter: SplitInt::<u64>::zero(),
			timezone: timezone,
			timezone_minutes: timezone_minutes,
	};
	if force {
		pi.next();
	}
        let shared = std::sync::Arc::new((
		std::sync::atomic::AtomicBool::new(false),
		std::sync::Mutex::new(pi),
	));

        let (winner_rx, forcers) = { // ensure winner_tx is dropped
                let (winner_tx, winner_rx) = std::sync::mpsc::channel();
                let mut forcers = Vec::new();
                for _i in 0..cpu {
                        let tx = winner_tx.clone();
                        let or = obj.clone();
                        let prefixbin = prefixbin.clone();
                        let shared = shared.clone();
                        forcers.push(std::thread::spawn(move || {
                                brute_force(or, tx, prefixbin, prefixbits, shared)
                        }));
                }
                (winner_rx, forcers)
        };

        let w = winner_rx.recv().map_err(|e| errmap("winner recv failed: ", &e))?;
        if verbose {
                println!("{:?}", w);
        }
        shared.0.store(true, std::sync::atomic::Ordering::SeqCst);
        for f in forcers.into_iter() {
                f.join().map_err(|e| errmap("forcer join", &format!("{:?}", e)))?;
        }

	git_env(verbose, &["commit", "--allow-empty", "--amend", &format!("--date={}", w.author), "--reuse-message=HEAD"], &vec![("GIT_COMMITTER_DATE".to_owned(), w.committer)]).map_err(|s| errmap("Failed to amend git object.", &s))?;

	if verbose {
		println!("new hash: {}", cur_hash(verbose).map_err(|e| errmap("new hash", &e))?);
	}
	Ok(())
}

fn git(verbose: bool, args: &[&str]) -> Result<Vec<u8>, String> {
	git_env(verbose, args, &vec![])
}

fn git_env(verbose: bool, args: &[&str], envs: &[(String, String)]) -> Result<Vec<u8>, String> {
	if verbose {
		println!("executing git{}", args.iter().fold("".to_owned(), |a, e| format!("{} '{}'", a, e)));
	}

        let mut obj = std::process::Command::new("git");
	let mut obj = obj.args(args);
	for env in envs {
		obj = obj.env(env.0.clone(), env.1.clone());
	}
	let obj = obj.output();

	if obj.is_err() || obj.iter().map(|o| o.status.success()).collect::<Vec<_>>() == vec![false] {
		let stderr = if obj.is_ok() { String::from_utf8_lossy(&obj.unwrap().stderr).to_string() } else { "".to_string() };
		Err(format!( "failure while executing git{}{}"
			, args.iter().fold("".to_owned(), |a, e| format!("{} '{}'", a, e))
			, stderr))
	} else {
		obj
			.map_err(|e| format!("{:?}", e))
			.and_then(|o| Ok(o.stdout))
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

fn cur_hash(verbose: bool) -> Result<String, String> {
	git(verbose, &["rev-parse", "HEAD"]).map(|o| String::from_utf8_lossy(&o).to_string())
}

#[derive(Debug)]
struct SplitInt<T> {
	i1: T,
	i2: T,
}

trait Zero {
	fn zero() -> Self;
}

trait Inc {
	fn inc(&mut self) -> ();
}

impl <T: Zero> Zero for SplitInt<T> {
	fn zero() -> Self {
		SplitInt{i1: T::zero(), i2: T::zero()}
	}
}

impl <T: Inc + Zero + Clone + PartialOrd> Inc for SplitInt<T> {
	fn inc(&mut self) -> () {
		let mut i1inc = self.i1.clone();
		i1inc.inc();
		if i1inc < self.i2 {
			self.i1.inc();
		} else if self.i2 < self.i1 {
			self.i2.inc();
		} else if self.i1 < self.i2 {
			self.i1.inc();
			self.i2 = T::zero();
		} else {
			self.i1 = T::zero();
			self.i2.inc();
		}
	}
}

impl Zero for u64 {
	fn zero() -> Self { 0 }
}

impl Inc for u64 {
	fn inc(&mut self) { *self += 1; }
}

struct PossibilityIterator {
	serial: u64,
	possibility_counter: SplitInt<u64>,
	timezone: bool,
	timezone_minutes: bool,
}

impl Iterator for PossibilityIterator {
	type Item = Possibility;
	fn next(&mut self) -> Option<Self::Item> {
		let ao = Offset::from_u64(self.possibility_counter.i1, self.timezone, self.timezone_minutes);
		let co = Offset::from_u64(self.possibility_counter.i2, self.timezone, self.timezone_minutes);

		self.serial += 1;
		self.possibility_counter.inc();

		Some(Possibility{serial: self.serial, author: ao, committer: co})
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

const TZMOD: u64 = 1+(12*60-1)*2; // {zero} U {+/- almost twelve hours}
const TZMODQ: u64 = 1+(12*4-1)*2; // {zero} U {+/- almost twelve hours in quarter hour steps}
impl Offset {
	fn from_u64(v: u64, timezone: bool, timezone_minutes: bool) -> Offset {
		let (modulus, tzmultiplier) =
			if timezone_minutes {
				(TZMOD, 1)
			} else if timezone {
				(TZMODQ, 15)
			} else {
				(1, 1)
			};
			
		let tz = (v + 1) % modulus;
		let t  = (v + 1) / modulus;
		fn parity_sign(v: u64) -> i32 {
			if v % 2 == 0 {
				(v >> 1) as i32
			} else {
				-((v >> 1) as i32)
			}
		}
		Offset{time_offset: parity_sign(t), timezone_offset: parity_sign(tz)*tzmultiplier}
	}
}

#[derive(Debug)]
struct Possibility {
	serial: u64,
        author: Offset,
        committer: Offset,
}

fn brute_force(obj: Vec<u8>, winner_tx: std::sync::mpsc::Sender<Solution>, prefixbin: Vec<u8>, prefixbits: usize, shared: std::sync::Arc<(std::sync::atomic::AtomicBool, std::sync::Mutex<PossibilityIterator>)>) -> () {
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

	fn tzadd(base_mins: i32, offset: i32) -> i32 {
                let mut res = base_mins + offset;
                if res < -12*60 {
                        res = 12*60 + (res + 12*60);
                } else if res > 12*60 {
                        res = -12*60 + (res - 12*60); 
                }
		res
	}

        fn tzformat(tz: i32) -> String {
                let ptz = tz.abs();
                format!("{}{:0>2}{:0>2}", if tz < 0 { '-' } else { '+' }, ptz / 60, ptz % 60)
        }

	fn inplace_format(dest: &mut [u8], mut time: i64, mut tz: i32) -> Result<(), ()> {
		let sign = if tz < 0 { b'-' } else { b'+' };
		tz = tz.abs();

		for i in 0..dest.len() {
			       if i == dest.len() - 1 {
				dest[i] = b'0' + (tz % 10) as u8;
			} else if i == dest.len() - 2 {
				dest[i] = b'0' + (tz % 60 / 10) as u8;
			} else if i == dest.len() - 3 {
				dest[i] = b'0' + (tz / 60 % 10) as u8;
			} else if i == dest.len() - 4 {
				dest[i] = b'0' + (tz / 60 / 10) as u8;
			} else if i == dest.len() - 5 {
				dest[i] = sign;
			} else if i == dest.len() - 6 {
			} else {
				if time == 0 {
					return Err(());
				}
				dest[dest.len() - i - 7] = b'0' + (time % 10) as u8;
				time /= 10;
			}
		}

		if time != 0 {
			Err(())
		} else {
			Ok(())
		}
	}

        let mut s1 = crypto::sha1::Sha1::new();
        let mask: Vec<u8> = make_mask(prefixbits);

        fn splice(dst: &mut [u8], offset: usize, src: &[u8]) {
                for (d, s) in dst.iter_mut().skip(offset).zip(src.iter()) {
                        *d = *s;
                }
        }

        //fn dump(tag: &str, b: &[u8]) { println!("{}: >{}<", tag, std::str::from_utf8(b).unwrap()); }
	let mut ad = format!("{} {}", ad_base, tzformat(tzadd(adtz_base, 0))).into_bytes();
	let mut cd = format!("{} {}", cd_base, tzformat(tzadd(cdtz_base, 0))).into_bytes();
        while let Ok(Some(p)) = shared.1.lock().map(|mut possibilities| possibilities.next()) {
                //println!("trying {:?}", p);
		let ad_utc = ad_base + p.author.time_offset as i64;
		let cd_utc = cd_base + p.committer.time_offset as i64;
		let ad_local = ad_base + p.author.time_offset as i64 + tzadd(adtz_base, p.author.timezone_offset) as i64;
		let cd_local = cd_base + p.committer.time_offset as i64 + tzadd(cdtz_base, p.committer.timezone_offset) as i64;
		if ad_local < 0 || cd_local < 0 || ad_utc < 0 || cd_utc < 0 {
                        continue;
                }

		if inplace_format(&mut ad, ad_base + p.author.time_offset as i64, tzadd(adtz_base, p.author.timezone_offset)).is_err() ||
			inplace_format(&mut cd, cd_base + p.committer.time_offset as i64, tzadd(cdtz_base, p.committer.timezone_offset)).is_err() {
			ad = format!("{} {}", ad_base + p.author.time_offset as i64, tzformat(tzadd(adtz_base, p.author.timezone_offset))).into_bytes();
			cd = format!("{} {}", cd_base + p.committer.time_offset as i64, tzformat(tzadd(cdtz_base, p.committer.timezone_offset))).into_bytes();
		}

                if ad.len() == adlen && cd.len() == cdlen {
                        splice(&mut blob, cdatei, &cd);
                        splice(&mut blob, adatei, &ad);
                } else {
                        //dump("extending blob", &blob);

                        let objlen: usize = vec![before_author_date, &ad, between_dates, &cd, after_committer_date].into_iter().map(|s| s.len()).sum();
                        intro = format!("commit {}\0", objlen).as_bytes().to_owned();

                        blob = Vec::with_capacity(objlen + intro.len());
                        for s in vec![&intro as &[u8], before_author_date, &ad, between_dates, &cd, after_committer_date] {
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

                if shared.0.load(std::sync::atomic::Ordering::SeqCst) {
                        break;
                }

                if matches_with_mask(&hash, &prefixbin, &mask) {
                        let winner = Solution{generated: p.serial, author: format!("@{}", String::from_utf8(ad).unwrap()), committer: format!("@{}", String::from_utf8(cd).unwrap())};
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
