import PfaffianDescent.CorayAllDegreeAffineOpenExt
import PfaffianDescent.SheafModuleMayerVietoris
import PfaffianDescent.SectionRepresenterTop
import PfaffianDescent.ExtMapFixedSource
import PfaffianDescent.VoisinStandardOpenExtVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! Native finite-cover cohomological dimension, derived by successive genuine
Mayer–Vietoris sequences, affine QC acyclicity, and actual affine intersections
on a separated scheme. This does NOT truncate ordered-tuple Cech: that complex
remains unbounded. No vanishing conclusion is an input to the public roots.
SOURCE ONLY / UNVERIFIED. Root owns compiler and audit. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite
universe u

/-- A union of N+1 ACTUAL affine opens on a separated locally noetherian
scheme has section-representer Ext vanishing in degrees at least N+1.
All intersection vanishing is derived recursively from actual affine geometry. -/
theorem affineFiniteNonemptyUnion_ext_subsingleton
    {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] (M : X.Modules) [M.IsQuasicoherent]
    (N : ℕ) (U : Fin (N + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (hq : N + 1 ≤ q) :
    Subsingleton (Ext.{u}
      (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf
        (⨆ i, U i)) M q) := by
  classical
  let originalExt : HasExt.{u} X.Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := originalExt
  induction N generalizing q with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = k + 1 := ⟨q - 1, by omega⟩
    have hopen : (⨆ i : Fin 1, U i) = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        exact hi ▸ le_rfl
      · exact le_iSup U 0
    have hvan := sectionRepresenter_ext_succ_subsingleton_of_isAffineOpen
      (U 0) (hU 0) M k
    have htransport := congrArg
      (fun V : X.Opens => Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf V)
        M (k + 1))) hopen
    exact Eq.mpr htransport hvan
  | succ N ih =>
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = k + 1 := ⟨q - 1, by omega⟩
    let V : Fin (N + 1) → X.Opens := fun i => U i.castSucc
    let W : X.Opens := U (Fin.last (N + 1))
    let A : X.Opens := ⨆ i, V i
    have hV : ∀ i, IsAffineOpen (V i) := fun i => hU i.castSucc
    have hW : IsAffineOpen W := hU (Fin.last (N + 1))
    have hsup : (⨆ i : Fin (N + 1 + 1), U i) = A ⊔ W := by
      apply le_antisymm
      · apply iSup_le
        intro i
        by_cases hi : i.val < N + 1
        · let j : Fin (N + 1) := ⟨i.val, hi⟩
          have heq : j.castSucc = i := Fin.ext rfl
          rw [← heq]
          exact (le_iSup V j).trans le_sup_left
        · have heq : i = Fin.last (N + 1) := by
            apply Fin.ext
            simp only [Fin.val_last]
            have hiBound := i.isLt
            omega
          rw [heq]
          exact le_sup_right
      · apply sup_le
        · exact iSup_le fun i => le_iSup U i.castSucc
        · exact le_iSup U (Fin.last (N + 1))
    have hinter : A ⊓ W = ⨆ i : Fin (N + 1), V i ⊓ W :=
      iSup_inf_eq V W
    have hVA : ∀ i : Fin (N + 1), IsAffineOpen (V i ⊓ W) :=
      fun i => (hV i).inf hW
    have hinterVan := ih (fun i : Fin (N + 1) => V i ⊓ W) hVA k (by omega)
    have hinterTransport := congrArg
      (fun B : X.Opens => Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf B)
        M k)) hinter
    letI hInterExt : Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf (A ⊓ W))
        M k) := Eq.mpr hinterTransport hinterVan
    letI hAExt : Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf A)
        M (k + 1)) := ih V hV (k + 1) (by omega)
    letI hWExt : Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf W)
        M (k + 1)) :=
      sectionRepresenter_ext_succ_subsingleton_of_isAffineOpen W hW M k
    have hvan := @PfaffianDescent.sectionRepresenter_ext_subsingleton_sup.{u}
      X inferInstance X.ringCatSheaf inferInstance inferInstance originalExt
      M A W k (k + 1) rfl hInterExt hAExt hWExt
    have htransport := congrArg
      (fun B : X.Opens => Subsingleton (Ext.{u}
        (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf B)
        M (k + 1))) hsup
    exact Eq.mpr htransport hvan

/-- A genuine cover by N+1 actual affine opens yields native sheaf
cohomological dimension at most N for EVERY actual quasicoherent module. -/
theorem schemeModuleCohomology_subsingleton_of_finiteAffineCover
    {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] (M : X.Modules) [M.IsQuasicoherent]
    (N : ℕ) (U : Fin (N + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (q : ℕ) (hq : N + 1 ≤ q) :
    Subsingleton (PfaffianDescent.schemeModuleCohomology X M q) := by
  have hvan := affineFiniteNonemptyUnion_ext_subsingleton M N U hU q hq
  have htransport := congrArg
    (fun V : X.Opens => Subsingleton (Ext.{u}
      (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf V)
      M q)) hcover
  letI : Subsingleton (Ext.{u}
      (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf (⊤ : X.Opens))
      M q) := Eq.mp htransport hvan
  exact PfaffianDescent.ext_subsingleton_of_iso_left
    (PfaffianDescent.sectionRepresenterTopIsoUnit X) q

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native projective-three-space cohomology vanishes in EVERY degree at
least four for EVERY quasicoherent sheaf. The standard affine four-cover,
its actual coverage, separatedness, and local noetherianity are derived;
no cohomological-dimension/vanishing or Cech-comparison certificate is input. -/
theorem p3_quasicoherent_cohomology_subsingleton_ge_four
    (K : Type u) [Field K]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules)
    [M.IsQuasicoherent] (q : ℕ) (hq : 4 ≤ q) :
    Subsingleton (PfaffianDescent.schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) M q) := by
  letI : IsLocallyNoetherian
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :=
    PfaffianDescent.ProjectiveNegativeTwist.p3_isLocallyNoetherian K
  let U := PfaffianDescent.ProjectiveNegativeTwist.p3StandardOpen (K := K)
  have hU : ∀ i : Fin 4, IsAffineOpen (U i) := by
    intro i
    change IsAffineOpen (Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (MvPolynomial.X i))
    exact Proj.isAffineOpen_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 4) K)
      (MvPolynomial.X i) (m := 1) (MvPolynomial.isHomogeneous_X K i) (by omega)
  exact schemeModuleCohomology_subsingleton_of_finiteAffineCover M 3 U hU
    (PfaffianDescent.ProjectiveNegativeTwist.p3StandardOpen_iSup K) q hq

end PfaffianDescent.Coray
