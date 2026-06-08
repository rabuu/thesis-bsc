#import "deps.typ": theorion

#import theorion: definition
#import theorion.cosmos.simple: definition

#let theorem-config(it) = {
  show: theorion.show-theorion

  theorion.set-theorion-numbering("1.1")
  theorion.set-inherited-levels(1)

  it
}
