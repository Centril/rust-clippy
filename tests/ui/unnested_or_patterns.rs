#![feature(or_patterns)]
#![feature(box_patterns)]
#![warn(clippy::unnested_or_patterns)]

fn main() {
    let x = Some(Some(0));
    match x {
        //box 0 | (box 1) => {}, // OK
        //box ((0 | 1)) | box (2 | 3) | box 4 => {}, // OK
        //box (0 | 1) | (box 2 | box (3 | 4)) => {}, // FAIL!
        //&0 | &mut 1 | &2 => {}, // OK
        // x @ 0 | x @ 1 => {}, // OK
        // (0, 1) | (0, 2) | (0, 3) => {}, // OK
        // [x, 0] | [x, 1] => {},
        // [0] | [1] => {},
        // Foo(0, x) | Foo(1, x) => {}, // OK.
        // IN_THE_WAY | Foo { x: 0 } | Foo { x: 1 } => {},
        // IN_THE_WAY | box 0 | box 1 => {}, // OK.
        Some(Some(0) | Some(1)) => {},
        _ => {},
    }
}
