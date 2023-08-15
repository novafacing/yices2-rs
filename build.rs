use anyhow::{anyhow, bail, ensure, Result};
use flate2::read::GzDecoder;
use std::{
    env::var,
    ffi::OsStr,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use tar::Archive;
use xz::read::XzDecoder;

const CUDD: &str = "cudd-3.0.0.tar.gz";
const GMP: &str = "gmp-6.3.0.tar.xz";
const POLY: &str = "libpoly-0.1.13.tar.gz";
const YICES: &str = "yices-2.6.4-src.tar.gz";

fn check_command(command: &mut Command) -> Result<()> {
    command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .map_err(|e| anyhow!("Failed to execute command: {}", e))
        .and_then(|r| {
            if r.status.success() {
                Ok(())
            } else {
                Err(anyhow!(
                    "Command failed with status code {}:\nstdout: {}\nstderr: {}",
                    r.status,
                    String::from_utf8_lossy(&r.stdout),
                    String::from_utf8_lossy(&r.stderr)
                ))
            }
        })
}

fn cargo_manifest_dir() -> Result<PathBuf> {
    var("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .map_err(|e| anyhow!("Couldn't get CARGO_MANIFEST_DIR: {}", e))
}

fn out_dir() -> Result<PathBuf> {
    var("OUT_DIR")
        .map(PathBuf::from)
        .map_err(|e| anyhow!("Couldn't get OUT_DIR: {}", e))
}

/// Unpack a compressed archive into the build directory.
///
/// If the resulting directory does not have the same name as the archive's stem,
/// an error is returned.
///
fn unpack_to_out<P>(src: P) -> Result<PathBuf>
where
    P: AsRef<Path>,
{
    let compressed = File::open(src.as_ref()).map_err(|e| {
        anyhow!(
            "Unable to open compressed file '{}' for unpacking: {}",
            src.as_ref().display(),
            e
        )
    })?;

    let deflate = match src.as_ref().extension().ok_or_else(|| {
        anyhow!(
            "No extension found for compressed source file '{}'",
            src.as_ref().display()
        )
    })? {
        ext if ext == "gz" => Box::new(GzDecoder::new(compressed)) as Box<dyn Read>,
        ext if ext == "xz" => Box::new(XzDecoder::new(compressed)) as Box<dyn Read>,
        ext => {
            return Err(anyhow!(
                "Unknown extension '{:?}' for compressed source file '{}'. Expected 'gz' or 'xz'.",
                ext,
                src.as_ref().display()
            ))
        }
    };

    let archive_path = src.as_ref().file_stem().map(PathBuf::from).ok_or_else(|| {
        anyhow!(
            "No file stem for compressed source file '{}'",
            src.as_ref().display()
        )
    })?;

    let mut unarchive = match archive_path.extension().ok_or_else(|| {
        anyhow!(
            "No extension for archived source file '{}'",
            archive_path.display()
        )
    })? {
        ext if ext == "tar" => Archive::new(deflate),
        ext => {
            return Err(anyhow!(
                "Unknown extension '{:?}' for archived source file '{}'. Expected 'tar'.",
                ext,
                archive_path.display()
            ))
        }
    };

    unarchive.unpack(out_dir()?)?;

    ensure!(
        out_dir()?
            .join(archive_path.file_stem().ok_or_else(|| anyhow!(
                "No stem for archived source file '{}'",
                archive_path.display()
            ))?)
            .is_dir(),
        "Archive did not unpack to expected directory {}",
        out_dir()?
            .join(archive_path.file_stem().ok_or_else(|| anyhow!(
                "No stem for archived source file '{}'",
                archive_path.display()
            ))?)
            .display()
    );

    Ok(out_dir()?.join(archive_path.file_stem().ok_or_else(|| {
        anyhow!(
            "No stem for archived source file '{}'",
            archive_path.display()
        )
    })?))
}

fn cc_name() -> Result<String> {
    if let Ok(compiler) = var("CC") {
        Ok(compiler)
    } else if var("CARGO_FEATURE_CLANG").is_ok() {
        Ok("clang".to_string())
    } else if var("CARGO_FEATURE_GCC").is_ok() {
        Ok("gcc".to_string())
    } else {
        bail!("No compiler specified in features or 'CC' environment variable");
    }
}

fn cxx_name() -> Result<String> {
    if let Ok(compiler) = var("CXX") {
        Ok(compiler)
    } else if var("CARGO_FEATURE_CLANG").is_ok() {
        Ok("clang++".to_string())
    } else if var("CARGO_FEATURE_GCC").is_ok() {
        Ok("g++".to_string())
    } else {
        bail!("No compiler specified in features or 'CXX' environment variable");
    }
}

fn check_prerequisites() -> Result<()> {
    // Global
    check_command(Command::new("make").arg("--version"))?;
    check_command(Command::new(cc_name()?).arg("--version"))?;
    check_command(Command::new(cxx_name()?).arg("--version"))?;
    // For CUDD
    check_command(Command::new("cmake").arg("--version"))?;

    Ok(())
}

fn main() -> Result<()> {
    check_prerequisites()?;
    let third_party = cargo_manifest_dir()?.join("third-party");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=third-party/*");

    unpack_to_out(third_party.join(GMP))?;
    unpack_to_out(third_party.join(CUDD))?;
    unpack_to_out(third_party.join(POLY))?;
    unpack_to_out(third_party.join(YICES))?;
    Ok(())
}
