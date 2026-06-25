{
  inputs = {
    llzk-pkgs.url = "github:project-llzk/llzk-nix-pkgs";
    nixpkgs.follows = "llzk-pkgs/nixpkgs";
    flake-utils.follows = "llzk-pkgs/flake-utils";
    llzk-lib.follows = "llzk-rs-pkgs/llzk-lib";
    release-helpers.follows = "llzk-lib/release-helpers";

    llzk-rs-pkgs = {
      url = "github:project-llzk/llzk-rs/main";
      inputs = {
        nixpkgs.follows = "llzk-pkgs/nixpkgs";
        flake-utils.follows = "llzk-pkgs/flake-utils";
        llzk-pkgs.follows = "llzk-pkgs";
      };
    };
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  # Custom colored bash prompt
  nixConfig.bash-prompt = "\\[\\e[0;32m\\][airbender]\\[\\e[m\\] \\[\\e[38;5;244m\\]\\w\\[\\e[m\\] % ";

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      release-helpers,
      llzk-pkgs,
      llzk-lib,
      llzk-rs-pkgs,
      rust-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            llzk-pkgs.overlays.default
            llzk-lib.overlays.default
            llzk-rs-pkgs.overlays.default
            release-helpers.overlays.default
            rust-overlay.overlays.default
          ];
        };

        # Lit tests need FileCheck but directly adding the LLVM `bin` dir to the path causes
        # linking problems in `llzk-sys`. Instead, create a symlink in a new directory for the path.
        createFileCheckSymlink = ''
          mkdir -p $PWD/build-tools
          ln -sf "${pkgs.llzk-llvmPackages.llvm}/bin/FileCheck" $PWD/build-tools/FileCheck
          export PATH="$PWD/build-tools:$PATH"
        '';

        rustToolchain = pkgs.rust-bin.nightly."2026-02-10".default;
        rustPlatform = pkgs.makeRustPlatform {
          rustc = rustToolchain;
          cargo = rustToolchain;
        };
      in
      {
        packages = flake-utils.lib.flattenTree {
          default = pkgs.rustPlatform.buildRustPackage (
            {
              pname = "airbender-to-llzk";
              version = "0.1.0";
              src = ./.;

              nativeBuildInputs = pkgs.llzkSharedEnvironment.nativeBuildInputs;
              buildInputs = pkgs.llzkSharedEnvironment.devBuildInputs;
              cargoLock = {
                lockFile = ./Cargo.lock;
                allowBuiltinFetchGit = true;
              };

              cargoBuildFlags = [
                "--package"
                "llzk_backend"
              ];
              cargoTestFlags = [
                "--package"
                "llzk_backend"
              ];
              preBuild = createFileCheckSymlink;
              LLZK_SYS_10_PREFIX = "${pkgs.llzk}";
            }
            // pkgs.llzkSharedEnvironment.env
            // pkgs.llzkSharedEnvironment.pkgSettings
          );
        };

        devShells = flake-utils.lib.flattenTree {
          default = pkgs.mkShell (
            {
              nativeBuildInputs = [ rustToolchain pkgs.pre-commit ] ++ pkgs.llzkSharedEnvironment.nativeBuildInputs;
              buildInputs = pkgs.llzkSharedEnvironment.devBuildInputs;

              shellHook = ''
                ## Bail out of pipes where any command fails
                set -uo pipefail
                ${createFileCheckSymlink}
                export LLZK_SYS_10_PREFIX="${pkgs.llzk}"
                echo "Welcome to the airbender-to-llzk devshell!"

                # set up pre-commit
                pre-commit install

                echo "To commit without pre-commit hooks, use \`git commit --no-verify\`"
              '';
            }
            // pkgs.llzkSharedEnvironment.env
            // pkgs.llzkSharedEnvironment.devSettings
          );
        };
      }
    );
}
