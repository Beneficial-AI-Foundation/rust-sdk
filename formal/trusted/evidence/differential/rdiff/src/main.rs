// Rust side of the differential check (run.sh): base64 0.23.1 URL_SAFE_NO_PAD and
// std String::from_utf8 / as_bytes, one output line per input, same format as Diff.lean.in.
use base64::{Engine, engine::general_purpose::URL_SAFE_NO_PAD};
use std::io::{BufRead, BufWriter, Write};

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" { return vec![]; }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}
fn hex(b: &[u8]) -> String {
    if b.is_empty() { return "-".into(); }
    b.iter().map(|x| format!("{:02x}", x)).collect()
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    let out = std::io::stdout();
    let mut o = BufWriter::new(out.lock());
    match mode {
        "enc_exh" => {
            for n in 0..=3u32 {
                for v in 0..(1u64 << (8 * n)) {
                    let b: Vec<u8> = (0..n).rev().map(|i| (v >> (8 * i)) as u8).collect();
                    let mut s = String::new();
                    URL_SAFE_NO_PAD.encode_string(&b, &mut s);
                    writeln!(o, "{}", if s.is_empty() { "-" } else { &s }).unwrap();
                }
            }
        }
        "utf8_exh" => {
            for n in 1..=2u32 {
                for v in 0..(1u64 << (8 * n)) {
                    let b: Vec<u8> = (0..n).rev().map(|i| (v >> (8 * i)) as u8).collect();
                    match String::from_utf8(b) {
                        Ok(s) => writeln!(o, "S {}", hex(s.as_bytes())).unwrap(),
                        Err(_) => writeln!(o, "N").unwrap(),
                    }
                }
            }
            // 3-byte exhaustive for leads E0..EF and C0..DF? all leads >= 0x80
            for v in 0x800000u64..0x1000000 {
                let b = vec![(v >> 16) as u8, (v >> 8) as u8, v as u8];
                match String::from_utf8(b) {
                    Ok(s) => writeln!(o, "S {}", hex(s.as_bytes())).unwrap(),
                    Err(_) => writeln!(o, "N").unwrap(),
                }
            }
        }
        _ => {
            let f = std::fs::File::open(&args[2]).unwrap();
            for line in std::io::BufReader::new(f).lines() {
                let line = line.unwrap();
                match mode {
                    "enc" => {
                        let mut s = String::new();
                        URL_SAFE_NO_PAD.encode_string(&unhex(&line), &mut s);
                        writeln!(o, "{}", if s.is_empty() { "-" } else { &s }).unwrap();
                    }
                    "enc_prefix" => {
                        // encode into a nonempty String to check append semantics
                        let mut s = String::from("x.");
                        URL_SAFE_NO_PAD.encode_string(&unhex(&line), &mut s);
                        writeln!(o, "{}", s).unwrap();
                    }
                    "dec" => match URL_SAFE_NO_PAD.decode(unhex(&line)).ok() {
                        Some(v) => writeln!(o, "S {}", hex(&v)).unwrap(),
                        None => writeln!(o, "N").unwrap(),
                    },
                    "utf8" => match String::from_utf8(unhex(&line)) {
                        Ok(s) => writeln!(o, "S {}", hex(s.as_bytes())).unwrap(),
                        Err(_) => writeln!(o, "N").unwrap(),
                    },
                    "cps" => {
                        let s: String = if line == "-" { String::new() } else {
                            line.split(',').map(|c| char::from_u32(u32::from_str_radix(c, 16).unwrap()).unwrap()).collect()
                        };
                        writeln!(o, "{}", hex(s.as_bytes())).unwrap();
                    }
                    _ => panic!("mode"),
                }
            }
        }
    }
}
