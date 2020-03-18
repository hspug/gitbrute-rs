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
	let (prefixbin, prefixmask, timezone, timezone_minutes, force, verbose, cpus) =
		config()?;

	let (winner_rx, forcers, done) =
		start_brute_force_threads(prefixbin, prefixmask, timezone, timezone_minutes, force, verbose, cpus)?;

	let winner = {
		let _signal = done;

        	winner_rx.recv().map_err(|e| errmap("winner recv failed: ", &e))?
	};
	
	cleanup(verbose, winner, forcers)
}

fn cleanup(verbose: bool, winner: Solution, forcers: Vec<std::thread::JoinHandle<()>>) -> Result<(), std::io::Error> {
        if verbose {
                println!("{:?} (approx bits: {})", winner, std::mem::size_of_val(&winner.generated) * 8 - clz(winner.generated * 3 / 2, 0, 1) - 1);
        }

        for f in forcers.into_iter() {
                f.join().map_err(|e| errmap("forcer join", &format!("{:?}", e)))?;
        }

	git_env(verbose, &["commit", "--allow-empty", "--amend", &format!("--date={}", winner.author), "--reuse-message=HEAD"], &vec![("GIT_COMMITTER_DATE".to_owned(), winner.committer)]).map_err(|s| errmap("Failed to amend git object.", &s))?;

	if verbose {
		println!("new hash: {}", cur_hash(verbose).map_err(|e| errmap("new hash", &e))?);
	}

	Ok(())
}

fn clz<T: Clone + PartialEq + std::ops::ShrAssign>(mut v: T, z: T, one: T) -> usize {
	let mut res = std::mem::size_of_val(&v) * 8;
	while v != z {
		res -= 1;
		v >>= one.clone();
	}
	res
}

fn start_brute_force_threads(prefixbin: Vec<u8>, prefixmask: Vec<u8>, timezone: bool, timezone_minutes: bool, force: bool, verbose: bool, cpus: usize) -> Result<(std::sync::mpsc::Receiver<Solution>, std::vec::Vec<std::thread::JoinHandle<()>>, scopeguard::ScopeGuard<(), impl FnOnce(()) -> ()>), std::io::Error> {
	let mut pi = PossibilityIterator{
			serial: 0,
			possibility_counter: SplitInt::<u64>::zero(),
			timezone: timezone,
			timezone_minutes: timezone_minutes,
	};
	if force {
		pi.next();
	}

        let done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let possibilities = std::sync::Arc::new(std::sync::Mutex::new(pi));

        let obj = git(verbose, &["cat-file", "-p", "HEAD"]).map_err(|e| errmap("failed to load git object for HEAD", &e))?;

	let (winner_tx, winner_rx) = std::sync::mpsc::channel();
	let mut forcers = Vec::new();
	for _ in 0..cpus {
		let tx = winner_tx.clone();
		let or = obj.clone();
		let prefixbin = prefixbin.clone();
		let prefixmask = prefixmask.clone();
		let done = done.clone();
		let possibilities = possibilities.clone();
		forcers.push(std::thread::spawn(move || {
			brute_force(or, tx, prefixbin, prefixmask, done, possibilities)
		}));
	}

	Ok((
		winner_rx,
		forcers,
		scopeguard::guard((), move |()| {
			if verbose {
				println!("setting done flag");
			}
			done.store(true, std::sync::atomic::Ordering::SeqCst);
		})
	))
}

fn config() -> Result<(Vec<u8>, Vec<u8>, bool, bool, bool, bool, usize), std::io::Error>{
        let matches = clap::App::new("gitbrute-rs").args_from_usage(
                        "--prefix=<deadbeef>     'Desired prefix.'
                        --prefix-bits=[num]      'Number of significant bits in the prefix.'
                        --prefix-mask=[ff008001] 'Bitmask of significant bits in the prefix.'
                        --timezone               'Allow timezone modifications at 15 minutes granularity.'
                        --timezone-minutes       'Allow timezone modifications at minute granularity.'
                        --force                  'Re-run, even if current hash matches prefix.'
                        --verbose                'Issue diagnostic messages.'
                        --cpus=[num]             'Number of CPUs to use. Defaults to number of processors.'")
                .get_matches();

        let verbose = matches.is_present("verbose");

        let prefix = matches.value_of("prefix").expect("--prefix arg is mandatory, clap-rs should have already been None-checked it.");
        if prefix.len() > 40 || prefix.chars().any(|c| !"0123456789abcdef".contains(c)) {
		return Err(errmap("Invalid prefix.", &""));
        }

        let prefixbits =
                matches.value_of("prefix-bits")
                .map(|s| s.parse().expect(&format!("wrong --prefix-bits value: {}", s)))
                .unwrap_or(prefix.len()*4);

	let prefixmask =
		matches.value_of("prefix-mask")
		.map(|s| rustc_hex::FromHex::from_hex(s).expect(&format!("wrong --prefix-mask value: {}", s)))
		.unwrap_or(make_mask(prefixbits));

	let prefixmask = prefixmask.into_iter().zip(make_mask(prefixbits)).map(|(pm, bm)| pm&bm).collect::<Vec<_>>();
		

        let prefixbin: Vec<_> = {
		let mut padded_prefix = prefix.to_owned();
		if prefix.len() % 2 == 1 {
			padded_prefix.push('0');
		};
                rustc_hex::FromHex::from_hex(padded_prefix.as_str()).expect(&format!("Invalid hexa prefix: {}", prefix))
        };

        if (prefixbits + 3) / 4 != prefix.len() {
                return Err(errmap("--prefix-bits don't correspond to prefix length", &format!(": ({} + 3) / 4 != {}", (prefixbits + 3) / 4, prefix.len())));
        }

        let force = matches.is_present("force");
        let timezone = matches.is_present("timezone");
        let timezone_minutes = matches.is_present("timezone-minutes");
        let cpus =
                matches.value_of("cpus")
                .map(|s| s.parse().expect(&format!("wrong cpus value: {}", s)))
                .unwrap_or(num_cpus::get());

	Ok((prefixbin, prefixmask, timezone, timezone_minutes, force, verbose, cpus))
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

trait /*std::num::*/Zero {
	fn zero() -> Self;
}

trait /*std::num::*/One {
	fn one() -> Self;
}

trait Inc {
	fn inc(&mut self) -> ();
}

impl <T: One + std::ops::AddAssign> Inc for T {
	fn inc(&mut self) -> () {
		*self += T::one();
	}
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

impl Zero for u64 { fn zero() -> Self { 0 } }
impl One  for u64 { fn one()  -> Self { 1 } }

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

const TZMODH: u64 = 1; // no timezones
const TZMODQ: u64 = 2*12*4 - 1; // +/- twelve hours in quarter hour steps, minus the full circle
const TZMODM: u64 = 2*12*60 - 1; // +/- twelve hours, minus the full circle
impl Offset {
	fn from_u64(v: u64, timezone: bool, timezone_minutes: bool) -> Offset {
		let (modulus, tzmultiplier) =
			if timezone_minutes {
				(TZMODM, 1)
			} else if timezone {
				(TZMODQ, 15)
			} else {
				(TZMODH, 60/*irrelevant, as tz is 0 in this case*/)
			};
			
		let tz = v % modulus + 1;
		let t  = v / modulus + 1;
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

fn brute_force(obj: Vec<u8>, winner_tx: std::sync::mpsc::Sender<Solution>, prefixbin: Vec<u8>, prefixmask: Vec<u8>, done: std::sync::Arc<std::sync::atomic::AtomicBool>, possibilities: std::sync::Arc<std::sync::Mutex<PossibilityIterator>>) -> () {
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

	fn tz_inplace(dest: &mut [u8], tz: i32) {
		dest[dest.len() - 5] = if tz < 0 { b'-' } else { b'+' };
		let tz = tz.abs();
		dest[dest.len() - 4] = b'0' + (tz / 60 / 10) as u8;
		dest[dest.len() - 3] = b'0' + (tz / 60 % 10) as u8;
		dest[dest.len() - 2] = b'0' + (tz % 60 / 10) as u8;
		dest[dest.len() - 1] = b'0' + (tz % 10) as u8;
	}

	fn inplace_format(dest: &mut [u8], mut time: i64, tz: i32) -> Result<(), ()> {
		tz_inplace(dest, tz);

		for i in 0..dest.len() - 6 {
			if time == 0 {
				return Err(());
			}

			dest[dest.len() - i - 7] = b'0' + (time % 10) as u8;

			time /= 10;
		}

		if time != 0 {
			Err(())
		} else {
			Ok(())
		}
	}

        let mut s1 = crypto::sha1::Sha1::new();

        fn splice(dst: &mut [u8], offset: usize, src: &[u8]) {
                for (d, s) in dst.iter_mut().skip(offset).zip(src.iter()) {
                        *d = *s;
                }
        }

        //fn dump(tag: &str, b: &[u8]) { println!("{}: >{}<", tag, std::str::from_utf8(b).unwrap()); }
	let mut ad = format!("{} {}", ad_base, tzformat(tzadd(adtz_base, 0))).into_bytes();
	let mut cd = format!("{} {}", cd_base, tzformat(tzadd(cdtz_base, 0))).into_bytes();
	let mut ad_utc_prev = ad_base;
	let mut cd_utc_prev = cd_base;
        while let Ok(Some(p)) = possibilities.lock().map(|mut possibilities| possibilities.next()) {
                //println!("trying {:?}", p);
		let ad_utc = ad_base + p.author.time_offset as i64;
		let cd_utc = cd_base + p.committer.time_offset as i64;
		let ad_tz = tzadd(adtz_base, p.author.timezone_offset);
		let cd_tz = tzadd(cdtz_base, p.committer.timezone_offset);
		let ad_local = ad_utc + ad_tz as i64;
		let cd_local = cd_utc + cd_tz as i64;
		if ad_local < 0 || cd_local < 0 || ad_utc < 0 || cd_utc < 0 {
                        continue;
                }

		if ad_utc_prev / 10 == ad_utc / 10 && cd_utc_prev / 10 == cd_utc / 10 {
			let ads: &mut [u8] = &mut ad;
			let cds: &mut [u8] = &mut cd;
			ads[ads.len() - 1 - 5 - 1] = b'0' + (ad_utc % 10) as u8;
			cds[cds.len() - 1 - 5 - 1] = b'0' + (cd_utc % 10) as u8;
			tz_inplace(&mut ad, ad_tz);
			tz_inplace(&mut cd, cd_tz);
		} else if inplace_format(&mut ad, ad_utc, ad_tz).is_err() ||
				inplace_format(&mut cd, cd_utc, cd_tz).is_err() {
			ad = format!("{} {}", ad_utc, tzformat(ad_tz)).into_bytes();
			cd = format!("{} {}", cd_utc, tzformat(cd_tz)).into_bytes();
		}
		ad_utc_prev = ad_utc;
		cd_utc_prev = cd_utc;

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

                if done.load(std::sync::atomic::Ordering::SeqCst) {
                        break;
                }

                if matches_with_mask(&hash, &prefixbin, &prefixmask) {
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
