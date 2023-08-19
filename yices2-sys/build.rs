use anyhow::{anyhow, bail, ensure, Result};
use bindgen::{Builder, CargoCallbacks, EnumVariation, RustTarget};
use flate2::read::GzDecoder;
use std::{
    env::var,
    fs::{create_dir_all, File},
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

const CUDD_OUT: &str = "cudd-3.0.0";
const GMP_OUT: &str = "gmp-6.3.0";
const POLY_OUT: &str = "libpoly-0.1.13";
const YICES_OUT: &str = "yices2-Yices-2.6.4";

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

fn prefix() -> Result<PathBuf> {
    let p = out_dir()?.join("prefix");

    if !p.is_dir() {
        create_dir_all(&p)?;
    }

    Ok(p)
}

/// Unpack a compressed archive into the build directory.
///
/// If the resulting directory does not have the same name as the archive's stem,
/// an error is returned.
///
fn unpack_to_out<P, S>(src: P, out: S) -> Result<PathBuf>
where
    P: AsRef<Path>,
    S: AsRef<str>,
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

    let result = out_dir()?.join(out.as_ref());

    ensure!(
        result.is_dir(),
        "Unpacked directory '{}' does not exist",
        result.display()
    );

    Ok(result)
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

fn build_gmp<P>(src: P) -> Result<()>
where
    P: AsRef<Path>,
{
    check_command(
        Command::new(src.as_ref().join("configure"))
            .current_dir(src.as_ref())
            .env("CC", cc_name()?)
            .env("CXX", cxx_name()?)
            .arg("--enable-assert=no")
            .arg("--enable-alloca=reentrant")
            // NOTE: libpoly needs GMP CXX
            .arg("--enable-cxx=yes")
            .arg("--enable-assembly=yes")
            .arg("--enable-fft=yes")
            .arg("--enable-old-fft-full=no")
            .arg("--enable-nails=no")
            .arg("--enable-profiling=no")
            .arg("--enable-fat=no")
            .arg("--enable-minithres=no")
            .arg("--enable-fake-cpuid=no")
            .arg("--enable-shared=no")
            .arg("--enable-static=yes")
            .arg("--enable-fast-install=yes")
            .arg("--with-readline=no")
            .arg("--with-pic=yes")
            .arg(format!("--prefix={}", prefix()?.display()))
            .arg(format!("--exec-prefix={}", prefix()?.display())),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .current_dir(src.as_ref()),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .arg("install")
            .current_dir(src.as_ref()),
    )?;

    Ok(())
}

fn build_cudd<P>(src: P) -> Result<()>
where
    P: AsRef<Path>,
{
    check_command(
        Command::new(src.as_ref().join("configure"))
            .current_dir(src.as_ref())
            .env("CC", cc_name()?)
            .env("CXX", cxx_name()?)
            .arg("--with-pic=yes")
            .arg("--disable-dependency-tracking")
            .arg(format!("--prefix={}", prefix()?.display()))
            .arg(format!("--exec-prefix={}", prefix()?.display())),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .current_dir(src.as_ref()),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .arg("install")
            .current_dir(src.as_ref()),
    )?;

    Ok(())
}

fn build_poly<P>(src: P) -> Result<()>
where
    P: AsRef<Path>,
{
    let build_dir = src.as_ref().join("build");

    if !build_dir.is_dir() {
        create_dir_all(&build_dir)?;
    }

    check_command(
        Command::new("cmake")
            .current_dir(&build_dir)
            .env("CC", cc_name()?)
            .env("CXX", cxx_name()?)
            .arg("-S")
            .arg(src.as_ref())
            .arg("-B")
            .arg(&build_dir)
            .arg("-DCMAKE_BUILD_TYPE=Release")
            .arg(format!("-DCMAKE_INSTALL_PREFIX={}", prefix()?.display()))
            .arg("-DLIBPOLY_BUILD_PYTHON_API=OFF")
            .arg("-DLIBPOLY_BUILD_STATIC_PIC=ON")
            .arg("-DLIBPOLY_BUILD_STATIC=ON")
            .arg("-DLIBPOLY_BUILD_STATISTICS=OFF")
            .arg(format!(
                "-DCMAKE_C_FLAGS=-I{}",
                prefix()?.join("include").display()
            ))
            .arg(format!(
                "-DCMAKE_CXX_FLAGS=-I{}",
                prefix()?.join("include").display()
            ))
            .arg(format!(
                "-DCMAKE_LIBRARY_PATH={}",
                prefix()?.join("lib").display()
            )),
    )?;

    check_command(
        Command::new("cmake")
            .current_dir(&build_dir)
            .arg("--build")
            .arg(&build_dir),
    )?;

    check_command(
        Command::new("cmake")
            .current_dir(&build_dir)
            .arg("--install")
            .arg(&build_dir),
    )?;

    Ok(())
}

fn build_yices2<P>(src: P) -> Result<()>
where
    P: AsRef<Path>,
{
    check_command(
        Command::new("autoconf")
            .current_dir(src.as_ref())
            .arg("-f")
            .arg(format!("-o{}", src.as_ref().join("configure").display()))
            .arg(src.as_ref().join("configure.ac")),
    )?;

    check_command(
        Command::new(src.as_ref().join("configure"))
            .current_dir(src.as_ref())
            .env("CC", cc_name()?)
            .env("CXX", cxx_name()?)
            .env("LDFLAGS", format!("-L{}", prefix()?.join("lib").display()))
            // NOTE: C PreProcessor flags
            .env(
                "CPPFLAGS",
                format!("-I{}", prefix()?.join("include").display()),
            )
            .env(
                "CFLAGS",
                format!("-I{}", prefix()?.join("include").display()),
            )
            .arg("--enable-mcsat")
            .arg(format!(
                "--with-static-gmp={}",
                prefix()?.join("lib").join("libgmp.a").display()
            ))
            .arg(format!(
                "--with-static-gmp-include-dir={}",
                prefix()?.join("include").display()
            ))
            .arg(format!(
                "--with-static-libpoly={}",
                prefix()?.join("lib").join("libpoly.a").display()
            ))
            .arg(format!(
                "--with-static-libpoly-include-dir={}",
                prefix()?.join("include").display()
            ))
            .arg(format!("--prefix={}", prefix()?.display()))
            .arg(format!("--exec-prefix={}", prefix()?.display())),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .current_dir(src.as_ref()),
    )?;

    check_command(
        Command::new("make")
            .arg(format!("-j{}", num_cpus::get()))
            .arg("install")
            .current_dir(src.as_ref()),
    )?;

    Ok(())
}

fn generate_bindings() -> Result<()> {
    let bindings = Builder::default()
        .header(
            prefix()?
                .join("include")
                .join("yices_exit_codes.h")
                .display()
                .to_string(),
        )
        .header(
            prefix()?
                .join("include")
                .join("yices_limits.h")
                .display()
                .to_string(),
        )
        .header(
            prefix()?
                .join("include")
                .join("yices_types.h")
                .display()
                .to_string(),
        )
        .header(
            prefix()?
                .join("include")
                .join("yices.h")
                .display()
                .to_string(),
        )
        .default_enum_style(EnumVariation::Rust {
            non_exhaustive: false,
        })
        .enable_function_attribute_detection()
        .disable_nested_struct_naming()
        .layout_tests(true)
        .impl_debug(true)
        .impl_partialeq(true)
        .derive_copy(true)
        .derive_debug(true)
        .derive_default(true)
        .derive_hash(true)
        .derive_partialord(true)
        .derive_ord(true)
        .derive_partialeq(true)
        .derive_eq(true)
        .anon_fields_prefix("__bindgen_anon_")
        .parse_callbacks(Box::new(CargoCallbacks))
        .generate_comments(true)
        .generate_cstr(true)
        .rust_target(RustTarget::Stable_1_68)
        .size_t_is_usize(true)
        .translate_enum_integer_types(true)
        .c_naming(false)
        .explicit_padding(true)
        .vtable_generation(true)
        .sort_semantically(true)
        .wrap_unsafe_ops(true)
        .clang_arg("-fparse-all-comments")
        .generate()?;

    bindings.write_to_file(out_dir()?.join("bindings.rs"))?;

    Ok(())
}

fn main() -> Result<()> {
    check_prerequisites()?;
    let third_party = cargo_manifest_dir()?.join("third-party");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=third-party/*");

    let gmp_src = unpack_to_out(third_party.join(GMP), GMP_OUT)?;
    let cudd_src = unpack_to_out(third_party.join(CUDD), CUDD_OUT)?;
    let poly_src = unpack_to_out(third_party.join(POLY), POLY_OUT)?;
    let yices_src = unpack_to_out(third_party.join(YICES), YICES_OUT)?;

    if !prefix()?.join("lib").join("libgmp.a").is_file() {
        build_gmp(gmp_src)?;
    }

    if !prefix()?.join("lib").join("libcudd.a").is_file() {
        build_cudd(cudd_src)?;
    }

    if !prefix()?.join("lib").join("libpoly.a").is_file() {
        build_poly(poly_src)?;
    }

    if !prefix()?.join("lib").join("libyices.a").is_file() {
        build_yices2(yices_src)?;
    }

    println!(
        "cargo:rustc-link-search=native={}",
        prefix()?.join("lib").display()
    );
    println!("cargo:rustc-link-lib=static=yices");
    println!("cargo:rustc-link-lib=static=gmp");
    println!("cargo:rustc-link-lib=static=cudd");
    println!("cargo:rustc-link-lib=static=poly");

    generate_bindings()?;

    Ok(())
}
