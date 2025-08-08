# MPCal Pygments

Pygments plugin for MPCal.

## Install

Run the following commands in the `pygments` directory:
```shell
pip install -r requirements.txt
sudo python3 setup.py develop
```

## Lexers

There are two available lexers:

* `mpcal`: 
  For highlighting MPCal code blocks.
* `tla+`:
  TLA+ highlighting that supports PlusCal and MPCal languages in the comments.

## Usage

You can use this plugin with command line. For example, output an HTML file, `output.html`, from an 
input TLA file, `/path/to/input.tla`:
```shell
pygmentize -f html -O full -o output.html /path/to/input.tla
```

For syntax highlighting inside Latex docuemtns, we use [minted](https://ctan.org/pkg/minted?lang=en) package. For more
information see the provided [example](latex/main.tex).

### Overleaf
To use the MPCal and TLA+ lexers provided here on [Overleaf](overleaf.com):
1. Upload the `mpcallexer/lexer.py` file to your Overleaf project's top-most level (i.e., root directory).
2. Change your TeX Live version to 2022 or earlier, see (link)[https://www.overleaf.com/learn/latex/Code_Highlighting_with_minted#Custom_lexers].
3. Use `\begin{minted}{lexer.py:TLAplusLexer -x}` to redirect highlighting to the custom lexer.
   - For TLA+: `{lexer.py:TLAPlusLexer -x}`
   - For MPCal: `{lexer.py:MPCalLexer -x}`
