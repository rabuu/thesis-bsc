VIEWER := "okular"
ENTRY := "thesis.typ"
ARTIFACT := "thesis.pdf"

alias c := compile
alias w := watch
alias o := open
alias wo := watch-open
alias fmt := format

compile:
	typst compile {{ENTRY}}

watch:
	typst watch {{ENTRY}}

open:
	{{VIEWER}} {{ARTIFACT}} &

watch-open: compile open watch

format:
	typstyle --inplace .

check-format:
	typstyle --check .

clean:
	fd --no-ignore -e pdf -x rm -v {}

configure-git-hooks:
	git config core.hooksPath scripts/git-hooks
