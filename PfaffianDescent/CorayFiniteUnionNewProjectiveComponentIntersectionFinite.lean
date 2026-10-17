import PfaffianDescent.CorayDistinctProjectiveCurveComponentIntersectionFinite
import PfaffianDescent.IntrinsicFiniteCycle
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range

/-! SOURCE ONLY / UNVERIFIED. An actual finite scheme-theoretic component
union has finite scheme-theoretic intersection with a distinct new curve
component. Actual whole ideals and all nilpotents are retained; no ideal
lattice distributivity, finite-intersection or degree certificate is supplied.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem homogeneousIdeal_finsetInf_toIdeal
    (F : Finset (HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))) :
    (F.inf id).toIdeal = F.inf (fun D => D.toIdeal) := by
  simp only [Finset.inf_eq_iInf, HomogeneousIdeal.toIdeal_iInf, id_eq]

/-- A finite actual union intersects a distinct new actual minimal curve
component in a finite scheme, INCLUDING its nonreduced intersection structure.
The native dimension input here is derived in the primitive selected caller. -/
theorem homogeneousFiniteUnion_newCurveComponent_sup_isFinite
    (I C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (F : Finset (HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)))
    (hC : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hCrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hFmin : ∀ D ∈ F, D.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hFrel : ∀ D ∈ F,
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ D)
    (hnew : C ∉ F)
    (hdim : ∀ x : scheme C, ringKrullDim ((scheme C).presheaf.stalk x) ≤ 1) :
    IsFinite (toBase (F.inf id ⊔ C)) := by
  classical
  let Z (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :
      Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :=
    ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) K) (C ⊔ D).toIdeal
  have hZfinite (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hDF : D ∈ F) : (Z D).Finite := by
    have hne : C ≠ D := by
      intro h
      exact hnew (h.symm ▸ hDF)
    letI : IsFinite (toBase (C ⊔ D)) :=
      homogeneousDistinctCurveComponents_sup_isFinite I C D hC hCrel
        (hFmin D hDF) (hFrel D hDF) hne hdim
    letI : IsArtinianScheme (scheme (C ⊔ D)) := finiteScheme_isArtinian (toBase (C ⊔ D))
    let j : scheme (C ⊔ D) →
        ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
      fun x => quotientProjMap (C ⊔ D) x
    have hrange : Set.range j = Z D := range_quotientProjMap (C ⊔ D)
    exact hrange ▸ Set.finite_range j
  let S : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :=
    ⋃ D : ↥F, Z D.1
  have hSfinite : S.Finite := Set.finite_iUnion (fun D : ↥F => hZfinite D.1 D.2)
  let H := F.inf id ⊔ C
  let j : scheme H → ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    fun x => quotientProjMap H x
  have hj : Function.Injective j := (quotientProjMap H).isClosedEmbedding.injective
  have hpoints (x : scheme H) : j x ∈ S := by
    let a : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) := j x
    let P := a.asHomogeneousIdeal.toIdeal
    have hHP : H.toIdeal ≤ P :=
      (quotientProjMap_mem_range_iff H a).mp ⟨x, rfl⟩
    have hCP : C.toIdeal ≤ P := le_sup_right.trans hHP
    have hUP : (F.inf id).toIdeal ≤ P := le_sup_left.trans hHP
    rw [homogeneousIdeal_finsetInf_toIdeal] at hUP
    have hPprime : P.IsPrime := a.isPrime
    obtain ⟨D, hDF, hDP⟩ := hPprime.inf_le'.mp hUP
    have ha : a ∈ Z D := by
      change (C.toIdeal ⊔ D.toIdeal) ≤ P
      exact sup_le hCP hDP
    exact Set.mem_iUnion.mpr ⟨⟨D, hDF⟩, ha⟩
  have hfiniteSource : (Set.univ : Set (scheme H)).Finite :=
    (hSfinite.preimage hj.injOn).subset (fun x _ => hpoints x)
  letI : LocallyQuasiFinite (toBase H) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (toBase H)
      (fun _ => hfiniteSource.subset (Set.subset_univ _))
  exact IsFinite.of_locallyQuasiFinite (toBase H)

/-- Primitive finite-union/new-component caller for the actual original
selected smooth cubic/degree-n intersection, allowing I to be any actual
homogeneous subscheme containing its two equations (e.g. a descended branch).
All native curve dimensions are derived; the finite family may be empty. -/
theorem selectedProjectiveFiniteUnion_newComponent_sup_isFinite
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (F : Finset (HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)))
    (hC : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hCrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hFmin : ∀ D ∈ F, D.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hFrel : ∀ D ∈ F,
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ D)
    (hnew : C ∉ F) : IsFinite (toBase (F.inf id ⊔ C)) := by
  exact homogeneousFiniteUnion_newCurveComponent_sup_isFinite
    I C F hC hCrel hFmin hFrel hnew
    (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
      p q hp hp0 n hq hnot C (hPQI.trans hC.1.2))

end PfaffianDescent.Coray
