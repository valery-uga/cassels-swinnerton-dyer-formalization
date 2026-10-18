import Mathlib.RingTheory.AdjoinRoot

/-! A coefficient-compatible embedding of root fields.
Its chosen root is mapped to the root of the coefficient-extended polynomial.
The target polynomial's irreducibility is retained explicitly. -/

noncomputable section
namespace AllCharacteristics
universe u v

/-- The quotient map induced by coefficient extension and an exact polynomial
identity. This is defined for arbitrary commutative coefficient rings. -/
def adjoinRootCoefficientMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) : AdjoinRoot p →+* AdjoinRoot q :=
  AdjoinRoot.map f p q (by simpa only [hpq] using (dvd_refl q))

@[simp] theorem adjoinRootCoefficientMap_root
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) :
    adjoinRootCoefficientMap f p q hpq (AdjoinRoot.root p) = AdjoinRoot.root q := by
  simp only [adjoinRootCoefficientMap, AdjoinRoot.map_root]

@[simp] theorem adjoinRootCoefficientMap_of
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) (r : R) :
    adjoinRootCoefficientMap f p q hpq (AdjoinRoot.of p r) =
      AdjoinRoot.of q (f r) := by
  simp only [adjoinRootCoefficientMap, AdjoinRoot.map_of]

theorem adjoinRootCoefficientMap_comp_of
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) :
    (adjoinRootCoefficientMap f p q hpq).comp (AdjoinRoot.of p) =
      (AdjoinRoot.of q).comp f := by
  ext r
  exact adjoinRootCoefficientMap_of f p q hpq r

/-- Irreducibility of both displayed polynomials gives an actual embedding
of their root fields. In particular the construction does not replace the
target by an unspecified algebraic closure. -/
theorem adjoinRootCoefficientMap_injective
    {R : Type u} {S : Type v} [Field R] [Field S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) (hp : Irreducible p) (hq : Irreducible q) :
    Function.Injective (adjoinRootCoefficientMap f p q hpq) := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : Fact (Irreducible q) := ⟨hq⟩
  exact (adjoinRootCoefficientMap f p q hpq).injective

end AllCharacteristics
