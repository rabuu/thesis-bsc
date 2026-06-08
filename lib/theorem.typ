#import "deps.typ": theorion

#import theorion: *
#import theorion.cosmos.simple: *

#let theorem-config(it) = {
  show: theorion.show-theorion

  set-theorion-numbering("1.1")
  set-inherited-levels(1)

  it
}
