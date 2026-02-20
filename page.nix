{ mkDerivation, standard-library }:

mkDerivation {
  pname = "inverses";
  version = "master";

  src = ./.;

  LC_ALL = "en_GB.UTF-8";

  buildInputs = [ standard-library ];

  buildPhase = ''
    agda --html --html-highlight=auto Everything.agda --css /css/Agda.css
    mv html/Everything.html html/index.html
  '';

  installPhase = ''
    mkdir -p $out
    cp html/*.html $out
  '';
}
