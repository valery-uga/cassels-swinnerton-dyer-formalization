import PfaffianDescent.AffineOpenCohomology

/-! ALL-degree affine-open section-representer Ext. Genuine open restriction,
injective embedding, actual flasque restriction and native covariant Ext
dimension shifting extend the existing low-degree comparison. The affine QC
caller derives all local vanishing from native affine QC acyclicity.
No global cohomological-dimension or desired vanishing certificate is input.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite
universe u

private theorem sectionRepresenter_ext_succ_of_restrict_acyclic
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    [HasExt.{u} X.Modules] [HasExt.{u} Z.Modules]
    (M : X.Modules)
    (hlocal : ∀ n : ℕ, Subsingleton (PfaffianDescent.schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) (n + 1))) (n : ℕ) :
    Subsingleton (Ext.{u}
      (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M (n + 1)) := by
  classical
  letI : EnoughInjectives X.Modules :=
    PfaffianDescent.sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : EnoughInjectives Z.Modules :=
    PfaffianDescent.sheafOfModules_enoughInjectives Z.ringCatSheaf
  induction n generalizing M with
  | zero =>
    letI := hlocal 0
    exact PfaffianDescent.sectionRepresenter_ext_one_subsingleton_of_restrict j M
  | succ n ih =>
    let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
    let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
    let P : X.Modules := PfaffianDescent.sectionRepresenter X.ringCatSheaf
      (j ''ᵁ (⊤ : Z.Opens))
    letI : F.PreservesZeroMorphisms := by infer_instance
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := by
      dsimp [S]
      exact { exact := ShortComplex.exact_cokernel I.f }
    have hSF : (S.map F).ShortExact :=
      PfaffianDescent.ShortComplex.shortExact_map_restrictFunctor j S hS
    letI : TopCat.Presheaf.IsFlasque I.J.val.presheaf :=
      PfaffianDescent.injective_isFlasque_scheme X I.J
    letI : TopCat.Presheaf.IsFlasque (F.obj I.J).val.presheaf := by
      dsimp [F]
      infer_instance
    have hlocalQ : ∀ m : ℕ, Subsingleton (PfaffianDescent.schemeModuleCohomology Z
        (F.obj (cokernel I.f)) (m + 1)) := by
      intro m
      letI : Subsingleton (Ext.{u} L (S.map F).X₂ (m + 1)) :=
        PfaffianDescent.flasque_schemeModuleCohomology_succ Z (F.obj I.J) m
      letI : Subsingleton (Ext.{u} L (S.map F).X₁ ((m + 1) + 1)) := hlocal (m + 1)
      exact PfaffianDescent.ext_subsingleton_of_middle_and_next_left L (S.map F) hSF (m + 1)
    letI : Subsingleton (Ext.{u} P S.X₃ (n + 1)) := ih (cokernel I.f) hlocalQ
    have hsurj : Function.Surjective ((Ext.mk₀ S.g).postcomp P (add_zero (n + 1))) := by
      intro q
      exact ⟨0, Subsingleton.elim _ _⟩
    letI : Subsingleton (Ext.{u} P S.X₂ ((n + 1) + 1)) :=
      Ext.subsingleton_of_injective P I.J (n + 1)
    exact PfaffianDescent.ext_succ_subsingleton_of_postcomp_surjective
      P S hS (n + 1) hsurj

/-- Genuine affine quasicoherent acyclicity transfers to the ACTUAL section
representer in EVERY positive degree. Only native affine/noetherian/QC
geometry is input; local vanishing is derived, not supplied. -/
theorem sectionRepresenter_ext_succ_subsingleton_of_isAffineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Ext.{u}
      (show X.Modules from PfaffianDescent.sectionRepresenter X.ringCatSheaf U) M (n + 1)) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let Z : Scheme.{u} := Spec R
  let j : Z ⟶ X := hU.fromSpec
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : EnoughInjectives Z.Modules :=
    PfaffianDescent.sheafOfModules_enoughInjectives Z.ringCatSheaf
  letI : HasExt.{u} Z.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Z.Modules
  letI : (F.obj M).IsQuasicoherent := by dsimp [F]; infer_instance
  have hlocal : ∀ m : ℕ, Subsingleton (PfaffianDescent.schemeModuleCohomology Z (F.obj M) (m + 1)) :=
    fun m => PfaffianDescent.affine_quasicoherent_cohomology_succ (R := R) (F.obj M) m
  have h := sectionRepresenter_ext_succ_of_restrict_acyclic j M hlocal n
  simpa only [j, Z, Scheme.Hom.image_top_eq_opensRange,
    IsAffineOpen.opensRange_fromSpec] using h

end PfaffianDescent.Coray
