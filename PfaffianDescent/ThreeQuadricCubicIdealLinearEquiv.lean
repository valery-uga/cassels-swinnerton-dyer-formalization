import PfaffianDescent.ThreeGeneratorKoszul
import PfaffianDescent.QuarticNetKoszul
import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.TripleCompleteIntersectionHilbert
import AllCharacteristics.SectionFour

/-! SOURCE ONLY / UNVERIFIED. The degree-three map of a genuine finite
three-quadric complete intersection. Bijectivity is proved, not assumed.
No etaleness/reducedness/cohomology hypothesis is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The literal cubic Koszul augmentation on polynomial homogeneous pieces. -/
def threeQuadricCubicIdealLinearMap (f g h : PS 2) :
    (PS 1 × PS 1 × PS 1) →ₗ[K]
      homogeneousIdealPiece
        (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
          f.property g.property h.property) 3 where
  toFun x := ⟨⟨f.val * x.1.val + g.val * x.2.1.val + h.val * x.2.2.val,
      ((f.property.mul x.1.property).add (g.property.mul x.2.1.property)).add
        (h.property.mul x.2.2.property)⟩, by
    change f.val * x.1.val + g.val * x.2.1.val + h.val * x.2.2.val ∈
      Ideal.span ({f.val, g.val, h.val} : Set (MvPolynomial (Fin 4) K))
    rw [← threeGeneratorLast_range]
    exact ⟨(x.1.val, x.2.1.val, x.2.2.val), rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change f.val * (x.1.val + y.1.val) + g.val * (x.2.1.val + y.2.1.val) +
      h.val * (x.2.2.val + y.2.2.val) =
      (f.val * x.1.val + g.val * x.2.1.val + h.val * x.2.2.val) +
        (f.val * y.1.val + g.val * y.2.1.val + h.val * y.2.2.val)
    ring
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      RingHom.id_apply, mul_smul_comm, smul_add]

lemma threeQuadricCubicIdealLinearMap_eq_zero_only
    (f g h : PS 2) (hf0 : f.val ≠ 0) (hrel : IsRelPrime f.val g.val)
    (hreg : ∀ a : MvPolynomial (Fin 4) K,
      h.val * a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K)))
    (x : PS 1 × PS 1 × PS 1) (hx : threeQuadricCubicIdealLinearMap f g h x = 0) :
    x = 0 := by
  have hraw : (x.1.val, x.2.1.val, x.2.2.val) ∈
      LinearMap.ker (threeGeneratorLast f.val g.val h.val) := by
    exact congrArg (fun z => z.val.val) hx
  rw [← threeGenerator_exact_last hf0 hrel hreg] at hraw
  obtain ⟨⟨r, s, t⟩, heq⟩ := hraw
  change (-g.val * r - h.val * s, f.val * r - h.val * t,
    f.val * s + g.val * t) = (x.1.val, x.2.1.val, x.2.2.val) at heq
  have hc (q : PS 2) (a : MvPolynomial (Fin 4) K) :
      homogeneousComponent 1 (q.val * a) = 0 := by
    rw [mul_comm]
    exact homogeneousComponent_mul_right_of_lt q.property (by decide)
  have hcn (q : PS 2) (a : MvPolynomial (Fin 4) K) :
      homogeneousComponent 1 (-q.val * a) = 0 := by
    rw [neg_mul, map_neg, hc, neg_zero]
  apply Prod.ext
  · apply Subtype.ext
    change x.1.val = 0
    have he := congrArg (homogeneousComponent 1) (congrArg Prod.fst heq)
    simpa only [map_sub, hcn, hc, sub_zero,
      homogeneousComponent_eq_self x.1.property] using he.symm
  · apply Prod.ext
    · apply Subtype.ext
      change x.2.1.val = 0
      have he := congrArg (homogeneousComponent 1)
        (congrArg (fun z : _ × _ × _ => z.2.1) heq)
      simpa only [map_sub, hc, sub_zero,
        homogeneousComponent_eq_self x.2.1.property] using he.symm
    · apply Subtype.ext
      change x.2.2.val = 0
      have he := congrArg (homogeneousComponent 1)
        (congrArg (fun z : _ × _ × _ => z.2.2) heq)
      simpa only [map_add, hc, add_zero,
        homogeneousComponent_eq_self x.2.2.property] using he.symm

/-- Regularity proves uniqueness; homogeneous projection proves existence. -/
def threeQuadricCubicIdealLinearEquivOfRegular
    (f g h : PS 2) (hf0 : f.val ≠ 0) (hrel : IsRelPrime f.val g.val)
    (hreg : ∀ a : MvPolynomial (Fin 4) K,
      h.val * a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K))) :
    (PS 1 × PS 1 × PS 1) ≃ₗ[K]
      homogeneousIdealPiece
        (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
          f.property g.property h.property) 3 := by
  apply LinearEquiv.ofBijective (threeQuadricCubicIdealLinearMap f g h)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply threeQuadricCubicIdealLinearMap_eq_zero_only f g h hf0 hrel hreg
    rw [map_sub, hxy, sub_self]
  · intro p
    obtain ⟨a, b, c, ha, hb, hc, heq⟩ :=
      QuarticNet.cubic_decomposition_of_mem_three_quadrics p.val.val
        f.val g.val h.val p.val.property f.property g.property h.property p.property
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact heq.symm

/-- Every finite nonempty triple has this actual cubic-piece isomorphism;
regularity and the absence of linear syzygies are internally derived. -/
def threeQuadricCubicIdealLinearEquivOfFinite
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))) :
    (PS 1 × PS 1 × PS 1) ≃ₗ[K]
      homogeneousIdealPiece
        (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
          f.property g.property h.property) 3 := by
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f.val g.val h.val f.property g.property h.property hT
  obtain ⟨hf0, hgreg, hhreg⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular f.val g.val h.val
      f.property g.property h.property).mp hseq
  exact threeQuadricCubicIdealLinearEquivOfRegular f g h hf0
    (isRelPrime_of_regular_mod_span_singleton hf0 hgreg) hhreg

end PfaffianDescent
