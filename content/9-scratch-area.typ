#import "/lib/lib.typ": *

#import syntax: *
#show: syntax.syntax-config

= Scratch Area

== Syntax for Linear Context Bindings
#bnf(
  (mark($q$), highlight[Quantity]),
  mark(alt(
    $1$,
    $omega quad "(mostly ommitted)"$,
  )),

  ($Gamma$, "Typing Contexts"),
  alt(
    $empty$,
    $Gamma, sp v :_mark(q)^chi tau$,
  ),
)

== Code Generation
$
  a2m(CREATE v = Gamma_0 sp b\; sp s) & := && STORE (REG_1 sp v) sp Gamma_0 & \
  & && LA (REG_2 sp v) sp l & \
  & && a2m(s) & \
  & && l: quad VTABLE sp b sp Gamma_0 & quad quad (l "fresh") \
  STORE r sp Gamma & := && STOREV Gamma & \
  &&& ACQUIRE r & \
  STOREV (Gamma, v :^chi tau) & := && SW (REG_2 sp v) sp (OFFSET_2 sp v) sp HEAP & \
  &&& SW (REG_1 sp v) sp (OFFSET_1 sp v) sp HEAP & \
  &&& STOREV Gamma \
  ACQUIRE r & := && MV r HEAP \
  &&& LW HEAP 0 HEAP \
  &&& BEQ HEAP #reg(0) l_1 \
  &&& quad SW #reg(0) 0 sp r \
  &&& quad JUMP l_2 \
  && l_1: & MV HEAP TODO \
  &&& LW TODO 0 TODO \
  &&& BEQ TODO #reg(0) l_3 \
  &&& quad SW #reg(0) 0 HEAP \
  &&& quad ERASEFIELDS HEAP \
  &&& quad JUMP l_2 \
  &&& l_3: ADDI TODO HEAP 32 \
  && l_2: & \
$
