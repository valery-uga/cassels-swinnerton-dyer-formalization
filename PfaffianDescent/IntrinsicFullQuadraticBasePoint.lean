import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.SectionFour
import AllCharacteristics.FiniteFieldCubicPoint

/-! Literal point existence from a finite FULL quadratic base locus of an
arbitrary, possibly nonreduced, length-eight subscheme.  The full-series
predicate is intrinsic and defined over every field.  Finite fields use the
checked Chevalley–Warning theorem; infinite fields select three members of
the actual full series and derive their scheme-theoretic containment. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def intrinsicFullQuadraticTripleIdeal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (q : Fin 3 → intrinsicFullQuadraticSystem i) :=
  tripleCompleteIntersectionHomogeneousIdeal (q 0).val (q 1).val (q 2).val
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 0).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 1).property)
    (intrinsicFullQuadraticSystem_homogeneous i _ (q 2).property)

/-- Every selected triple contains the original subscheme, directly through
its ideal-sheaf kernel.  No coordinate or containment premise is supplied. -/
theorem intrinsicFullQuadraticTripleIdeal_ker_le {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (q : Fin 3 → intrinsicFullQuadraticSystem i) :
    (quotientProjMap (intrinsicFullQuadraticTripleIdeal i q)).ker ≤ i.ker := by
  apply quotientProjMap_ker_le_of_intrinsic_chart_ideal
  intro j
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | rfl | rfl
  · exact ((Submodule.mem_iInf _).mp (q 0).property.2) j
  · exact ((Submodule.mem_iInf _).mp (q 1).property.2) j
  · exact ((Submodule.mem_iInf _).mp (q 2).property.2) j

theorem intrinsicFullQuadraticSystem_exists_finite_triple_containing
    [Infinite K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    ∃ q : Fin 3 → intrinsicFullQuadraticSystem i,
      IsFinite (toBase (intrinsicFullQuadraticTripleIdeal i q)) ∧
      ∃ l : Z ⟶ scheme (intrinsicFullQuadraticTripleIdeal i q),
      IsClosedImmersion l ∧
        l ≫ quotientProjMap (intrinsicFullQuadraticTripleIdeal i q) = i ∧
        l ≫ toBase (intrinsicFullQuadraticTripleIdeal i q) = i ≫ ambientToBase := by
  letI : IsFinite (toBase (quadraticSystemBaseLocusIdeal
      (intrinsicFullQuadraticSystem i) (intrinsicFullQuadraticSystem_homogeneous i))) :=
    inferInstanceAs (IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i)))
  obtain ⟨q, hfinite⟩ := exists_finite_triple_of_finite_full_quadratic_system
    (intrinsicFullQuadraticSystem i) (intrinsicFullQuadraticSystem_homogeneous i)
  let T := intrinsicFullQuadraticTripleIdeal i q
  let l := IsClosedImmersion.lift (quotientProjMap T) i
    (intrinsicFullQuadraticTripleIdeal_ker_le i q)
  have hfac : l ≫ quotientProjMap T = i := IsClosedImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (l ≫ quotientProjMap T) := by rw [hfac]; infer_instance
  have hl : IsClosedImmersion l := IsClosedImmersion.of_comp l (quotientProjMap T)
  refine ⟨q, hfinite, l, hl, hfac, ?_⟩
  rw [← quotientProjMap_toBase T, ← Category.assoc, hfac]

set_option backward.isDefEq.respectTransparency false in
/-- Proposition `prop:existence-of-point` in `2-proofs.tex`: finiteness of
the FULL quadratic base locus through a length-eight subscheme gives an
actual rational section of the cubic over an arbitrary field. -/
theorem sectionFour_section_of_cubic_of_finite_intrinsic_full_quadratic_base
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (j : Z ⟶ hypersurface F hF) [IsClosedImmersion j]
    [IsFinite (j ≫ hypersurfaceToBase F hF)]
    (hZ : AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F hF) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal (j ≫ hypersurfaceToAmbient F hF)))] :
    ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  rcases finite_or_infinite K with hfiniteK | hinfiniteK
  · letI : Finite K := hfiniteK
    exact finite_field_cubic_has_rational_section F hF
  · letI : Infinite K := hinfiniteK
    let a := j ≫ hypersurfaceToAmbient F hF
    obtain ⟨q, hfinite, l, hl, hambient, hbase⟩ :=
      intrinsicFullQuadraticSystem_exists_finite_triple_containing a
    letI := hl
    let hf := intrinsicFullQuadraticSystem_homogeneous a _ (q 0).property
    let hg := intrinsicFullQuadraticSystem_homogeneous a _ (q 1).property
    let hh := intrinsicFullQuadraticSystem_homogeneous a _ (q 2).property
    change Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      (q 0).val (q 1).val (q 2).val hf hg hh) at l
    change l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal
      (q 0).val (q 1).val (q 2).val hf hg hh) = a ≫ ambientToBase at hbase
    letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (q 0).val (q 1).val (q 2).val hf hg hh)) := hfinite
    let v := tripleCompleteIntersectionToHypersurface
      (q 0).val (q 1).val (q 2).val hf hg hh
    let i := l ≫ v
    have hbasei : i ≫ hypersurfaceToBase (q 0).val hf =
        j ≫ hypersurfaceToBase F hF := by
      change (l ≫ v) ≫ hypersurfaceToBase (q 0).val hf = _
      rw [Category.assoc, tripleCompleteIntersectionToHypersurface_toBase, hbase]
      change (j ≫ quotientProjMap (equationIdeal F hF)) ≫ ambientToBase = _
      rw [Category.assoc, quotientProjMap_toBase]
      rfl
    letI : IsClosedImmersion v := inferInstanceAs
      (IsClosedImmersion (tripleCompleteIntersectionToHypersurface
        (q 0).val (q 1).val (q 2).val hf hg hh))
    letI : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (l ≫ v))
    letI : IsFinite (i ≫ hypersurfaceToBase (q 0).val hf) := by
      rw [hbasei]
      infer_instance
    have hZi : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase (q 0).val hf) = 8 := by
      rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbasei,
        ← AllCharacteristics.finiteSchemeRank_eq_finrank]
      exact hZ
    apply AllCharacteristics.sectionFour_section_of_cubic_of_finite_nonempty_net
      F (q 0).val (q 1).val (q 2).val hF hf hg hh i (l.le_ker_comp v) hZi j
    change j ≫ hypersurfaceToAmbient F hF =
      (l ≫ v) ≫ hypersurfaceToAmbient (q 0).val hf
    rw [Category.assoc, tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
    exact hambient.symm

end PfaffianDescent
