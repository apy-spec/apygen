use apy::Apy;
use apygen_python_analysis::{AbsolutePathBuf, LocalFilesystem, analyse_workdir};
use std::fs::File;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let working_dir = AbsolutePathBuf::current_dir()?;
    let python_paths = vec![];
    let stubs_paths = vec![];
    let typeshed = Some(working_dir.join("vendor/typeshed/stdlib"));

    let apy: Apy = analyse_workdir(
        LocalFilesystem,
        python_paths,
        stubs_paths,
        working_dir,
        typeshed,
    );

    apy.to_yaml_writer(&mut File::create("apy.yaml")?)?;

    Ok(())
}
