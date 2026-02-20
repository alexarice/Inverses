{
  description = "Agda flake";

  inputs = {
    all-agda.url = "github:alexarice/all-agda";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, all-agda, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      agdaPackages = all-agda.legacyPackages."x86_64-linux".agdaPackages-2_6_1;
    in {
      packages = rec {
        page = agdaPackages.callPackage ./page.nix { };
        default = page;
      };
    }
  );
}
