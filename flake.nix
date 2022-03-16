{
  description = "challenges for CS2800";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOs/nixpkgs/nixos-unstable";
  };

  outputs = { self, ... }@inputs:
    with inputs;
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = (import nixpkgs { inherit system; });
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs;
            [ (agda.withPackages [ agdaPackages.standard-library ]) ];
        };
      });
}
