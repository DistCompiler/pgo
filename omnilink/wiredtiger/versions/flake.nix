{
  description = "WiredTiger for OmniLink";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    wiredtiger_11_3_1 = {
      type = "github";
      owner = "wiredtiger";
      repo = "wiredtiger";
      rev = "05c56015a42154ac8145366678a4f8eb419b5933";
      flake = false;
    };
    wiredtiger_lockbug = {
      type = "github";
      owner = "wiredtiger";
      repo = "wiredtiger";
      rev = "5ad9e6d37986c69e4adcce2863928ed39710b090";
      flake = false;
    };
  };

  outputs = { nixpkgs, wiredtiger_11_3_1, wiredtiger_lockbug, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      derivationForSrc = { version, src }: pkgs.stdenv.mkDerivation {
        version = version;
        pname = "wiredtiger";
        env.NIX_CFLAGS_COMPILE = "-Wno-error"; # or we get strange fireworks!
        cmakeFlags = [
          # unbreak .pc file
          "-DCMAKE_INSTALL_LIBDIR=lib"
          "-DCMAKE_INSTALL_INCLUDEDIR=include"
          # debug build in case something goes wrong
          "-DCMAKE_BUILD_TYPE=Debug"
        ];
        nativeBuildInputs = [
          pkgs.cmake
          pkgs.pkg-config
          pkgs.ninja
          pkgs.python3
          pkgs.swig
        ];
        src = src;
      };
    in {
    systems = [ "x86_64-linux" ];
    packages.x86_64-linux.v11_3_1 = derivationForSrc {
      version = "11.3.1";
      src = wiredtiger_11_3_1;
    };
    packages.x86_64-linux.lockbug = derivationForSrc {
      version = "lockbug";
      src = wiredtiger_lockbug;
    };
  };
}
