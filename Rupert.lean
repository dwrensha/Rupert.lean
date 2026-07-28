module

public import Rupert.Affine
public import Rupert.Attr
public import Rupert.Basic
public import Rupert.Convex
public import Rupert.Cube
public import Rupert.FinCases
public import Rupert.Icosahedron
public meta import Rupert.MatrixSimps
public import Rupert.Nopert214
public import Rupert.Quaternion
public import Rupert.Equivalences.RupertEquivRupertPrime
public import Rupert.Equivalences.RupertEquivRupertSet
public import Rupert.Equivalences.AffineRupertEquivRupertSet
public import Rupert.Set
public import Rupert.SnubCube
public import Rupert.Square
public import Rupert.Tetrahedron
public import Rupert.TriakisTetrahedron

@[expose] public section

--- main results

/--
info: 'Cube.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cube.rupert


/--
info: 'Tetrahedron.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tetrahedron.rupert


/--
info: 'TriakisTetrahedron.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TriakisTetrahedron.rupert

/--
info: 'Nopert214.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Nopert214.rupert
