use nesfile::File;
use std::path::Path;

#[test]
fn roms_parse() {
    let manifest_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    let roms_path = manifest_path.join("tests/roms-for-testing");
    std::fs::read_dir(&roms_path).unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "nes"))
        .for_each(|path| {
            let data = std::fs::read(&path).unwrap();
            let (i, _file) = File::parse(&data).unwrap();
            assert!(i.is_empty());
        });
}
