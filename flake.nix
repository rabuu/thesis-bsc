{
  description = "My bachelor thesis";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = pkgs.mkShell {
          name = "thesis";
          packages = with pkgs; [
            typst
            tinymist
            typstyle
            hayagriva
            just
            fd
          ];

          shellHook = "unset SOURCE_DATE_EPOCH";
        };
      }
    );
}
