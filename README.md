This is a fork of the [HoTT library](https://github.com/HoTT/HoTT) in
which we are formalizing the results in the paper:

- [CS] The Hurewicz Theorem in Homotopy Type Theory,
  J. Daniel Christensen and Luis Scoccola,
  [arxiv:2007.05833](https://arxiv.org/abs/2007.05833).
  To appear in Algebraic & Geometric Topology.

This README refers to the numbering that matches the numbering in v1 and v2 of that preprint.

The formalization in this Hurewicz branch is due to Dan Christensen and Ali Caglayan.
It is a work in progress, and still has many rough edges.
This snapshot is provided so that others can see the current progress.
Many of the results here will eventually be moved into appropriate files
in the main repository.

Most work is in the
[theories/Hurewicz](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz)
folder.
Here is a summary of the files in that folder, listed in an order that is compatible
with the dependencies.

- [Ptd.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/Ptd.v):
  This contains some simple facts about pointed maps that will be moved elsewhere.
- [ConnCover.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/ConnCover.v):
  This contains the material in [CS, Section 2.3].
- [PreGroup.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/PreGroup.v):
  This long file contains the basic theory of magmas,
  and proves results in the first part of [CS, Section 2.4].
  Among other things,
  Proposition 2.23 is `isequiv_magma_iterated_loops_functor_conn_trunc'`, and
  Lemma 2.24 is `equiv_magma_iterated_loops_in`.
  (The name `PreGroup` is a temporary name reflecting the fact that we study
  *weak* magma morphisms.)
- [PathGpd.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/PathGpd.v):
  This short file gives a new, slick proof of the Eckmann-Hilton theorem.
  (The existing proof is fine for our purposes, so this is tangential to the Hurewicz formalization.)
  It also includes an easy result, `horizontal_vertical1`, that is used later.
- [HomotopyGroup2.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/HomotopyGroup2.v):
  This short file defines a variant `Pi' n X` of the nth homotopy group of a type which
  is a group (abelian group) when n is 1 (at least 2).
- [Smashing.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/Smashing.v):
  This long file has proofs of further results in [CS, Section 2.4], leading up to [CS, Definition 2.26],
  the definition of the smashing map, which is called `smashing` in the formalization.
- [Smash2.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Hurewicz/Smash2.v):
  This proves more results from [CS, Section 2], such as
  Corollary 2.32 (`isconnected_smash`),
  Lemma 2.40 (`isequiv_swap`),
  Lemma 2.41 (`pswap_natural`),
  Lemma 2.42 (`isequiv_ptr_smash_functor`),
  Corollary 2.43 (`isequiv_ptr_smash_functor'`), and
  Lemma 2.44 (`pequiv_psusp_smash'`, without the naturality).

Some changes have been made to other files as well:

- [Abelianization.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Algebra/AbGroups/Abelianization.v)
- [Pointed/Core.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Pointed/Core.v)
- [Pointed/pHomotopy.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Pointed/pHomotopy.v)
- [Pointed/Loops.v](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/Pointed/Loops.v)
- [WildCat/*](https://github.com/jdchristensen/HoTT/tree/Hurewicz/theories/WildCat) (many files)

Finally, other changes have already been incorporated into the master branch of the HoTT library, and are not listed here.

In the paper, we define the sum `m + n` of natural numbers by induction on `n`,
so that `m+1` is the successor of `m`.
In the HoTT library, the other convention is used, so to translate between
the paper and the formalization, one must change `m+n` to `n+m` everywhere.

This version builds with Coq 8.14.0.  It doesn't build with 8.16.1.
