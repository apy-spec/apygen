use apy::Apy;
use apygen::analyse_workdir;
use apygen::finder::filesystem::{AbsolutePathBuf, LocalFilesystem};
use std::fs::File;
use std::process::Command;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let working_dir = AbsolutePathBuf::current_dir()?;

    let output = Command::new("python")
        .arg("-c")
        .arg("import sys; print(sys.path)")
        .output()?; // TODO: improve

    let python_paths = String::from_utf8(output.stdout)?
        .trim()
        .trim_start_matches('[')
        .trim_end_matches(']')
        .split(',')
        .map(|value| value.trim().trim_matches('\'').trim_matches('"'))
        .map(|path| working_dir.join(path))
        .collect::<Vec<_>>();

    let stubs_paths = vec![];
    let typeshed = Some(AbsolutePathBuf::current_dir()?.join("vendor/typeshed/stdlib"));

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
