use nesfile::File;
use std::path::Path;

#[test]
fn super_mario_bros_parses() {
    let manifest_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = manifest_path.join("tests/Super Mario Bros.nes");
    let data = std::fs::read(&path).unwrap();
    let (i, _file) = File::parse(&data).unwrap();
    assert!(i.is_empty());
}
