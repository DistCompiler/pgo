{
  description = "OmniLink Porcupine Eval Rig";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.default = pkgs.buildGoModule {
        name = "omnilink-porcupine-rig";
        vendorHash = "sha256-+lz7IAyY2L98SsZuJbFemZNPxc0/b6Tkqr07XMzcPPM=";
        src = ./.;
      };
    };
}
