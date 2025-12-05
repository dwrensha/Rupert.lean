# Rupert.lean

This project is a formalization of the
[Rupert Problem](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube) in
the [Lean](https://lean-lang.org/) theorem prover.

Roughly speaking, the problem asks:
given two congruent copies of a convex polyhedron,
can we cut a hole in one copy, such that the other copy fits through the hole?

## Main Results
|  |  |
| ----- | ---- |
|cube | [Rupert/Cube.lean](Rupert/Cube.lean) |
|tetrahedron | [Rupert/Tetrahedron.lean](Rupert/Tetrahedron.lean)|
|triakis tetrahedron | [Rupert/TriakisTetrahedron.lean](Rupert/TriakisTetrahedron.lean)|

## Related Projects

The [Noperthedron Project](https://github.com/jcreedcmu/Noperthedron)
is working on formalizing a proof that the [Noperthedron](https://arxiv.org/abs/2508.18475) is not Rupert.

## Videos

The proof for the triakis tetrahedron is explained in this video:

[<img src="http://img.youtube.com/vi/jDTPBdxmxKw/maxresdefault.jpg" height="300px">](https://youtu.be/jDTPBdxmxKw)

Known solutions for Platonic, Catalan, and Archimedean solids are
visualized in this video:

[<img src="http://img.youtube.com/vi/evKFok65t_E/maxresdefault.jpg" height="300px">](https://youtu.be/evKFok65t_E)

