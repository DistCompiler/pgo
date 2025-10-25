{
  description = "OmniLink WiredTiger Stressor";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    wiredtiger.url = ./versions;
    wiredtiger.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { nixpkgs, wiredtiger, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      forWtVersion = { version, wt }: pkgs.stdenv.mkDerivation {
        version = version;
        pname = "wt-stressor";
        buildInputs = [
          wt
          pkgs.msgpack-cxx
        ];
        nativeBuildInputs = [
          pkgs.pkg-config
          pkgs.cmake
        ];
      };
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.v11_3_1 = forWtVersion {
        version = "11.3.1";
        wt = wiredtiger.packages.x86_64-linux.v11_3_1;
      };
    };
}
