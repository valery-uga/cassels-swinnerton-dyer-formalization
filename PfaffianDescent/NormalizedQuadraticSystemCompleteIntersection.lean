import PfaffianDescent.HomogeneousProjectiveKernelSaturation
import PfaffianDescent.QuadraticFullBaseLocusFiniteTriple
import PfaffianDescent.HomogeneousVanishingLinearSystem
import PfaffianDescent.NormalizedFiniteEquationPoint
import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.SectionFour

/-! The full quadratic evaluation kernel of a finite algebra, including
nonreduced algebras.  Finiteness of its full base locus supplies an actual
three-quadric complete intersection; length eight identifies that intersection
with the original finite algebra and computes the full kernel's dimension. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- When a normalized equation map is an isomorphism and the homogeneous
ring has no irrelevant socle, homogeneous evaluation detects literal ideal
membership.  No reducedness assumption is involved. -/
theorem normalizedFiniteEquationPoint_mem_of_evaluation_zero
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    [IsIso (normalizedFiniteEquationPoint I x ell hell hellOne he)]
    (hsocle : ∀ a : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * a = 0) → a = 0)
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hpzero : p.eval₂ (algebraMap K A) x = 0) : p ∈ I.toIdeal := by
  let J := equationIdeal p hp
  have heJ : ∀ q ∈ J.toIdeal, q.eval₂ (algebraMap K A) x = 0 := by
    have hle : J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K A) x) := by
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact hpzero
    exact fun q hq => hle hq
  let l := normalizedFiniteEquationPoint I x ell hell hellOne he
  let r := normalizedFiniteEquationPoint J x ell hell hellOne heJ
  have hdiag : r ≫ hypersurfaceToAmbient p hp = l ≫ quotientProjMap I := by
    exact (normalizedFiniteEquationPoint_toAmbient J x ell hell hellOne heJ).trans
      (normalizedFiniteEquationPoint_toAmbient I x ell hell hellOne he).symm
  apply homogeneous_mem_of_hypersurface_ker_le_of_no_irrelevant_annihilator I p hp
  · apply hypersurface_ker_le_of_factor p hp (inv l ≫ r) (quotientProjMap I)
    rw [Category.assoc, hdiag]
    simp
  · exact hsocle

variable [Module.Finite K A]

def normalizedQuadraticSystem (x : Fin 4 → A) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  homogeneousVanishingPolynomialSubmodule x 2

theorem normalizedQuadraticSystem_homogeneous
    (x : Fin 4 → A) (p : MvPolynomial (Fin 4) K)
    (hp : p ∈ normalizedQuadraticSystem x) : p.IsHomogeneous 2 :=
  (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p).mp hp |>.1

def normalizedQuadraticBaseIdeal (x : Fin 4 → A) :=
  quadraticSystemBaseLocusIdeal (normalizedQuadraticSystem x)
    (normalizedQuadraticSystem_homogeneous x)

def normalizedQuadraticTripleIdeal (x : Fin 4 → A)
    (q : Fin 3 → normalizedQuadraticSystem x) :=
  tripleCompleteIntersectionHomogeneousIdeal (q 0).val (q 1).val (q 2).val
    (normalizedQuadraticSystem_homogeneous x _ (q 0).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 1).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 2).property)

theorem normalizedQuadraticTripleIdeal_evaluation_zero
    (x : Fin 4 → A) (q : Fin 3 → normalizedQuadraticSystem x) :
    ∀ p ∈ (normalizedQuadraticTripleIdeal x q).toIdeal,
      p.eval₂ (algebraMap K A) x = 0 := by
  have hle : (normalizedQuadraticTripleIdeal x q).toIdeal ≤
      RingHom.ker (eval₂Hom (algebraMap K A) x) := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 _).mp
        (q 0).property |>.2
    · exact (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 _).mp
        (q 1).property |>.2
    · exact (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 _).mp
        (q 2).property |>.2
  exact fun p hp => hle hp

/-- The rank-eight comparison, applied to the actual selected triple rather
than a supplied containment or complete-intersection certificate. -/
theorem normalizedQuadraticTriplePoint_isIso_of_finite
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hA : Module.finrank K A = 8) (q : Fin 3 → normalizedQuadraticSystem x)
    [IsFinite (toBase (normalizedQuadraticTripleIdeal x q))] :
    IsIso (normalizedFiniteEquationPoint (normalizedQuadraticTripleIdeal x q)
      x ell hell hellOne (normalizedQuadraticTripleIdeal_evaluation_zero x q)) := by
  let T := normalizedQuadraticTripleIdeal x q
  let l := normalizedFiniteEquationPoint T x ell hell hellOne
    (normalizedQuadraticTripleIdeal_evaluation_zero x q)
  letI : IsClosedImmersion l :=
    normalizedFiniteEquationPoint_isClosedImmersion T x ell hell hellOne _ hgen
  letI : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; decide)
  have hT : Nonempty (scheme T) := Nonempty.map l inferInstance
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    (q 0).val (q 1).val (q 2).val
    (normalizedQuadraticSystem_homogeneous x _ (q 0).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 1).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 2).property) hT
  have hT8 : AllCharacteristics.finiteSchemeRank (toBase T) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence _ _ _ _ _ _ hseq
  apply isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq l (toBase T)
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
    normalizedFiniteEquationPoint_toBase, Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A)) _).trans
    (hA.trans hT8.symm)

/-- Every finite triple selected from the full kernel has the same quadratic
piece as that kernel.  Saturation is derived from finite nonempty regularity. -/
theorem normalizedQuadraticSystem_eq_triple_quadratic_piece_of_finite
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hA : Module.finrank K A = 8) (q : Fin 3 → normalizedQuadraticSystem x)
    [IsFinite (toBase (normalizedQuadraticTripleIdeal x q))] :
    normalizedQuadraticSystem x =
      (homogeneousIdealPiece (normalizedQuadraticTripleIdeal x q) 2).map
        (homogeneousSubmodule (Fin 4) K 2).subtype := by
  let T := normalizedQuadraticTripleIdeal x q
  let heT := normalizedQuadraticTripleIdeal_evaluation_zero x q
  let l := normalizedFiniteEquationPoint T x ell hell hellOne heT
  letI : IsIso l :=
    normalizedQuadraticTriplePoint_isIso_of_finite x ell hell hellOne hgen hA q
  letI : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; decide)
  have hT : Nonempty (scheme T) := Nonempty.map l inferInstance
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    (q 0).val (q 1).val (q 2).val
    (normalizedQuadraticSystem_homogeneous x _ (q 0).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 1).property)
    (normalizedQuadraticSystem_homogeneous x _ (q 2).property) hT
  obtain ⟨hq0, hq1, hq2⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular _ _ _ _ _ _).mp hseq
  have hsocle : ∀ a : CoordinateRing T,
      (∀ j : Fin 4, coordinate T j * a = 0) → a = 0 :=
    triple_quadrics_no_irrelevant_annihilator _ _ _ _ _ _ hq0
      (right_ne_zero_of_regular_mod_span_singleton
        (homogeneous_not_isUnit_of_pos_degree
          (normalizedQuadraticSystem_homogeneous x _ (q 0).property) (by decide)) hq1)
      (isRelPrime_of_regular_mod_span_singleton hq0 hq1) hq2
  ext p
  constructor
  · intro hp
    obtain ⟨hp2, hpzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p).mp hp
    have hpT := normalizedFiniteEquationPoint_mem_of_evaluation_zero T x ell
      hell hellOne heT hsocle p hp2 hpzero
    exact ⟨⟨p, hp2⟩, hpT, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p.val).mpr
      ⟨p.property, heT p.val hp⟩

theorem normalizedQuadraticSystem_finrank_eq_three_of_finite_full_base
    [Infinite K] (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hellOne : ell.eval₂ (algebraMap K A) x = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hA : Module.finrank K A = 8)
    [IsFinite (toBase (normalizedQuadraticBaseIdeal x))] :
    Module.finrank K (normalizedQuadraticSystem x) = 3 := by
  obtain ⟨q, hfinite⟩ := exists_finite_triple_of_finite_full_quadratic_system
    (normalizedQuadraticSystem x) (normalizedQuadraticSystem_homogeneous x)
  letI := hfinite
  let T := normalizedQuadraticTripleIdeal x q
  let l := normalizedFiniteEquationPoint T x ell hell hellOne
    (normalizedQuadraticTripleIdeal_evaluation_zero x q)
  letI : Nontrivial A := Module.nontrivial_of_finrank_pos (by rw [hA]; decide)
  have hT : Nonempty (scheme T) := Nonempty.map l inferInstance
  rw [normalizedQuadraticSystem_eq_triple_quadratic_piece_of_finite
    x ell hell hellOne hgen hA q,
    Submodule.finrank_map_subtype_eq]
  exact AllCharacteristics.sectionFour_triple_quadric_ideal_quadratic_piece_dimension_three_of_finite_of_nonempty
    _ _ _ _ _ _ hT

end PfaffianDescent
