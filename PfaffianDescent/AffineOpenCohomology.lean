import PfaffianDescent.AffineQCAcyclicity
import PfaffianDescent.SheafModuleOverExtComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite AlgebraicGeometry

namespace PfaffianDescent

universe u

variable {X Z : Scheme.{u}}

/-- Restriction of a flasque module sheaf along any open immersion is flasque. -/
instance schemeModule_restrictFunctor_isFlasque_of_isOpenImmersion
    (j : Z ⟶ X) [IsOpenImmersion j] (I : X.Modules)
    [TopCat.Presheaf.IsFlasque I.val.presheaf] :
    TopCat.Presheaf.IsFlasque
      (((Scheme.Modules.restrictFunctor j).obj I).val.presheaf) where
  epi {V W} i := by
    letI : TopCat.Presheaf.IsFlasque I.presheaf := by
      change TopCat.Presheaf.IsFlasque I.val.presheaf
      infer_instance
    change Epi ((I.restrict j).presheaf.map i)
    rw [show i = i.unop.op by simp, Scheme.Modules.restrict_map]
    exact TopCat.Presheaf.IsFlasque.epi _

private lemma sectionRepresenterHomEquiv_postcomp'
    (j : Z ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules}
    (f : sectionRepresenter X.ringCatSheaf (j ''ᵁ (⊤ : Z.Opens)) ⟶ M)
    (g : M ⟶ N) :
    sectionRepresenterHomEquiv X.ringCatSheaf (j ''ᵁ (⊤ : Z.Opens)) N (f ≫ g) =
      g.val.app (op (j ''ᵁ (⊤ : Z.Opens)))
        (sectionRepresenterHomEquiv X.ringCatSheaf
          (j ''ᵁ (⊤ : Z.Opens)) M f) := by
  rfl

/-- Surjectivity after restriction along an open immersion transfers to
surjectivity from the object representing sections on its image. -/
theorem sectionRepresenter_postcomp_surjective_of_restrict_unit
    (j : Z ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (g : M ⟶ N)
    (hsurj : Function.Surjective
      (fun f : SheafOfModules.unit Z.ringCatSheaf ⟶
          (Scheme.Modules.restrictFunctor j).obj M =>
        f ≫ (Scheme.Modules.restrictFunctor j).map g)) :
    Function.Surjective
      (fun f : sectionRepresenter X.ringCatSheaf (j ''ᵁ (⊤ : Z.Opens)) ⟶ M =>
        f ≫ g) := by
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let T : Z.Opens := ⊤
  let hT : IsTerminal T := isTerminalTop
  intro q
  let y : N.val.obj (op (j ''ᵁ (⊤ : Z.Opens))) :=
    sectionRepresenterHomEquiv X.ringCatSheaf (j ''ᵁ (⊤ : Z.Opens)) N q
  let yLocal : (F.obj N).val.obj (op T) := y
  let qLocal : L ⟶ F.obj N :=
    (F.obj N).unitHomEquiv.symm
      ((moduleSectionsEquivTerminal T hT (F.obj N)).symm yLocal)
  obtain ⟨pLocal, hpLocal⟩ := hsurj qLocal
  let xLocal : (F.obj M).val.obj (op T) :=
    moduleSectionsEquivTerminal T hT (F.obj M)
      ((F.obj M).unitHomEquiv pLocal)
  let x : M.val.obj (op (j ''ᵁ (⊤ : Z.Opens))) := xLocal
  let p : sectionRepresenter X.ringCatSheaf (j ''ᵁ (⊤ : Z.Opens)) ⟶ M :=
    (sectionRepresenterHomEquiv X.ringCatSheaf
      (j ''ᵁ (⊤ : Z.Opens)) M).symm x
  refine ⟨p, ?_⟩
  apply (sectionRepresenterHomEquiv X.ringCatSheaf
    (j ''ᵁ (⊤ : Z.Opens)) N).injective
  rw [sectionRepresenterHomEquiv_postcomp']
  change g.val.app (op (j ''ᵁ (⊤ : Z.Opens)))
      ((sectionRepresenterHomEquiv X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens)) M)
        ((sectionRepresenterHomEquiv X.ringCatSheaf
          (j ''ᵁ (⊤ : Z.Opens)) M).symm x)) = y
  rw [Equiv.apply_symm_apply]
  change pLocal ≫ F.map g = qLocal at hpLocal
  have hpSections := congrArg (fun k => (F.obj N).unitHomEquiv k) hpLocal
  rw [SheafOfModules.unitHomEquiv_comp_apply pLocal (F.map g)] at hpSections
  have hpValue := congrArg
    (moduleSectionsEquivTerminal T hT (F.obj N)) hpSections
  rw [moduleSectionsEquivTerminal_naturality T hT (F.map g)
    ((F.obj M).unitHomEquiv pLocal)] at hpValue
  dsimp only [qLocal] at hpValue
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hpValue
  change g.val.app (op (j ''ᵁ (⊤ : Z.Opens))) x = y at hpValue
  exact hpValue

end PfaffianDescent


namespace PfaffianDescent

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite AlgebraicGeometry

variable {X Z : Scheme.{u}}

private theorem sectionRepresenter_ext_one_subsingleton_of_restrict_aux
    (j : Z ⟶ X) [IsOpenImmersion j]
    [EnoughInjectives X.Modules]
    [HasExt.{u} X.Modules]
    [HasExt.{u} Z.Modules]
    (M : X.Modules)
    [Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 1)] :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 1) := by
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let P : X.Modules := sectionRepresenter X.ringCatSheaf
    (j ''ᵁ (⊤ : Z.Opens))
  letI : F.PreservesZeroMorphisms := by infer_instance
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel I.f }
  have hSF : (S.map F).ShortExact :=
    ShortComplex.shortExact_map_restrictFunctor j S hS
  letI : Subsingleton (Ext.{u} L (S.map F).X₁ 1) := by
    change Subsingleton (schemeModuleCohomology Z (F.obj M) 1)
    infer_instance
  have hsurjLocal : Function.Surjective
      (fun f : L ⟶ F.obj S.X₂ => f ≫ F.map S.g) := by
    change Function.Surjective
      (fun f : L ⟶ (S.map F).X₂ => f ≫ (S.map F).g)
    exact hom_postcomp_surjective_of_ext_one_subsingleton L (S.map F) hSF
  have hsurjGlobal : Function.Surjective
      (fun f : P ⟶ S.X₂ => f ≫ S.g) := by
    change Function.Surjective
      (fun f : sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens)) ⟶ S.X₂ => f ≫ S.g)
    apply sectionRepresenter_postcomp_surjective_of_restrict_unit j S.g
    change Function.Surjective
      (fun f : L ⟶ F.obj S.X₂ => f ≫ F.map S.g)
    exact hsurjLocal
  exact ext_one_subsingleton_of_hom_postcomp_surjective P S hS hsurjGlobal

/-- Degree-one cohomology after restriction along an open immersion controls
Ext from the object representing sections on its image. -/
theorem sectionRepresenter_ext_one_subsingleton_of_restrict
    (j : Z ⟶ X) [IsOpenImmersion j]
    [HasExt.{u} X.Modules]
    [HasExt.{u} Z.Modules]
    (M : X.Modules)
    [Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 1)] :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 1) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact sectionRepresenter_ext_one_subsingleton_of_restrict_aux j M

attribute [local instance] Ext.subsingleton_of_injective

private theorem sectionRepresenter_ext_one_and_two_subsingleton_of_restrict_aux
    (j : Z ⟶ X) [IsOpenImmersion j]
    [EnoughInjectives X.Modules]
    [EnoughInjectives Z.Modules]
    [HasExt.{u} X.Modules]
    [HasExt.{u} Z.Modules]
    (M : X.Modules)
    (h₁ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 1))
    (h₂ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 2)) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 2) := by
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let P : X.Modules := sectionRepresenter X.ringCatSheaf
    (j ''ᵁ (⊤ : Z.Opens))
  letI : F.PreservesZeroMorphisms := by infer_instance
  letI : Subsingleton (Ext.{u} L (F.obj M) 1) := h₁
  have hGlobalOne : Subsingleton (Ext.{u} P M 1) := by
    exact sectionRepresenter_ext_one_subsingleton_of_restrict_aux j M
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel I.f }
  have hSF : (S.map F).ShortExact :=
    ShortComplex.shortExact_map_restrictFunctor j S hS
  letI : TopCat.Presheaf.IsFlasque I.J.val.presheaf :=
    injective_isFlasque_scheme X I.J
  letI : TopCat.Presheaf.IsFlasque (F.obj I.J).val.presheaf := by
    dsimp [F]
    infer_instance
  letI hFIone : Subsingleton (Ext.{u} L (F.obj I.J) 1) := by
    exact flasque_schemeModuleCohomology_one Z (F.obj I.J)
  letI : Subsingleton (Ext.{u} L (S.map F).X₂ 1) := by
    change Subsingleton (Ext.{u} L (F.obj I.J) 1)
    exact hFIone
  letI : Subsingleton (Ext.{u} L (S.map F).X₁ 2) := by
    change Subsingleton (Ext.{u} L (F.obj M) 2)
    exact h₂
  letI hFQone : Subsingleton (Ext.{u} L (F.obj (cokernel I.f)) 1) := by
    change Subsingleton (Ext.{u} L (S.map F).X₃ 1)
    exact ext_subsingleton_of_middle_and_next_left L (S.map F) hSF 1
  have hGlobalQone : Subsingleton (Ext.{u} P (cokernel I.f) 1) := by
    exact sectionRepresenter_ext_one_subsingleton_of_restrict_aux j (cokernel I.f)
  letI : Subsingleton (Ext.{u} P S.X₃ 1) := by
    change Subsingleton (Ext.{u} P (cokernel I.f) 1)
    exact hGlobalQone
  have hsurjOne : Function.Surjective
      ((Ext.mk₀ S.g).postcomp P (add_zero 1)) := by
    intro q
    exact ⟨0, Subsingleton.elim _ _⟩
  letI : Subsingleton (Ext.{u} P S.X₂ 2) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective P I.J 1
  have hGlobalTwo : Subsingleton (Ext.{u} P S.X₁ 2) :=
    ext_succ_subsingleton_of_postcomp_surjective P S hS 1 hsurjOne
  constructor
  · exact hGlobalOne
  · change Subsingleton (Ext.{u} P S.X₁ 2) at hGlobalTwo
    exact hGlobalTwo

/-- Low-degree cohomology on an open source controls Ext from the object
representing sections on the image of that open immersion. -/
theorem sectionRepresenter_ext_one_and_two_subsingleton_of_restrict
    (j : Z ⟶ X) [IsOpenImmersion j]
    [HasExt.{u} X.Modules]
    [HasExt.{u} Z.Modules]
    (M : X.Modules)
    (h₁ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 1))
    (h₂ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 2)) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 2) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : EnoughInjectives Z.Modules :=
    sheafOfModules_enoughInjectives Z.ringCatSheaf
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_restrict_aux j M h₁ h₂

/-- Cohomology through degree three after restriction along an open
immersion controls Ext from the object representing sections on its image. -/
theorem sectionRepresenter_ext_one_two_three_subsingleton_of_restrict
    (j : Z ⟶ X) [IsOpenImmersion j]
    [HasExt.{u} X.Modules]
    [HasExt.{u} Z.Modules]
    (M : X.Modules)
    (h₁ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 1))
    (h₂ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 2))
    (h₃ : Subsingleton (schemeModuleCohomology Z
      ((Scheme.Modules.restrictFunctor j).obj M) 3)) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 2) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf
        (j ''ᵁ (⊤ : Z.Opens))) M 3) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : EnoughInjectives Z.Modules :=
    sheafOfModules_enoughInjectives Z.ringCatSheaf
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  let L : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let P : X.Modules := sectionRepresenter X.ringCatSheaf
    (j ''ᵁ (⊤ : Z.Opens))
  letI : F.PreservesZeroMorphisms := by infer_instance
  have hlow := sectionRepresenter_ext_one_and_two_subsingleton_of_restrict_aux
    j M h₁ h₂
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel I.f }
  have hSF : (S.map F).ShortExact :=
    ShortComplex.shortExact_map_restrictFunctor j S hS
  letI : TopCat.Presheaf.IsFlasque I.J.val.presheaf :=
    injective_isFlasque_scheme X I.J
  letI : TopCat.Presheaf.IsFlasque (F.obj I.J).val.presheaf := by
    dsimp [F]
    infer_instance
  letI hFIone : Subsingleton (schemeModuleCohomology Z (F.obj I.J) 1) :=
    flasque_schemeModuleCohomology_one Z (F.obj I.J)
  letI hFItwo : Subsingleton (schemeModuleCohomology Z (F.obj I.J) 2) :=
    flasque_schemeModuleCohomology_two Z (F.obj I.J)
  letI : Subsingleton (Ext.{u} L (S.map F).X₂ 1) := by
    change Subsingleton (schemeModuleCohomology Z (F.obj I.J) 1)
    exact hFIone
  letI : Subsingleton (Ext.{u} L (S.map F).X₁ 2) := by
    change Subsingleton (schemeModuleCohomology Z (F.obj M) 2)
    exact h₂
  letI hFQone : Subsingleton (Ext.{u} L (F.obj (cokernel I.f)) 1) := by
    change Subsingleton (Ext.{u} L (S.map F).X₃ 1)
    exact ext_subsingleton_of_middle_and_next_left L (S.map F) hSF 1
  letI : Subsingleton (Ext.{u} L (S.map F).X₂ 2) := by
    change Subsingleton (schemeModuleCohomology Z (F.obj I.J) 2)
    exact hFItwo
  letI : Subsingleton (Ext.{u} L (S.map F).X₁ 3) := by
    change Subsingleton (schemeModuleCohomology Z (F.obj M) 3)
    exact h₃
  letI hFQtwo : Subsingleton (Ext.{u} L (F.obj (cokernel I.f)) 2) := by
    change Subsingleton (Ext.{u} L (S.map F).X₃ 2)
    exact ext_subsingleton_of_middle_and_next_left L (S.map F) hSF 2
  have hGlobalQlow :=
    sectionRepresenter_ext_one_and_two_subsingleton_of_restrict_aux
      j (cokernel I.f) hFQone hFQtwo
  letI : Subsingleton (Ext.{u} P S.X₃ 2) := by
    change Subsingleton (Ext.{u} P (cokernel I.f) 2)
    exact hGlobalQlow.2
  letI : Subsingleton (Ext.{u} P S.X₂ 2) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective P I.J 1
  have hsurjTwo : Function.Surjective
      ((Ext.mk₀ S.g).postcomp P (add_zero 2)) := by
    intro q
    exact ⟨0, Subsingleton.elim _ _⟩
  letI : Subsingleton (Ext.{u} P S.X₂ 3) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective P I.J 2
  have hGlobalThree : Subsingleton (Ext.{u} P S.X₁ 3) :=
    ext_succ_subsingleton_of_postcomp_surjective P S hS 2 hsurjTwo
  exact ⟨hlow.1, hlow.2, by
    change Subsingleton (Ext.{u} P S.X₁ 3) at hGlobalThree
    exact hGlobalThree⟩

end PfaffianDescent

namespace PfaffianDescent

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite AlgebraicGeometry

variable {X : Scheme.{u}}

/-- If a module becomes quasicoherent after pullback to the canonical
spectrum of an affine open, then its section-representer Ext vanishes there
in degrees one and two. -/
theorem sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict
    [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules)
    (hQC : ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let Z : Scheme.{u} := Spec R
  let j : Z ⟶ X := hU.fromSpec
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : EnoughInjectives Z.Modules :=
    sheafOfModules_enoughInjectives Z.ringCatSheaf
  letI : HasExt.{u} Z.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Z.Modules
  letI : (F.obj M).IsQuasicoherent := hQC
  have h₁ : Subsingleton (schemeModuleCohomology Z (F.obj M) 1) := by
    exact affine_quasicoherent_cohomology_one (R := R) (F.obj M)
  have h₂ : Subsingleton (schemeModuleCohomology Z (F.obj M) 2) := by
    exact affine_quasicoherent_cohomology_two (R := R) (F.obj M)
  have h := sectionRepresenter_ext_one_and_two_subsingleton_of_restrict
    j M h₁ h₂
  simpa [j, Z, IsAffineOpen.opensRange_fromSpec] using h

/-- Quasicoherent modules have vanishing section-representer Ext in degrees
one and two on every affine open of a locally noetherian scheme. -/
theorem sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen
    [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) := by
  apply sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict
    U hU M
  infer_instance

/-- If a module becomes quasicoherent after pullback to the canonical
spectrum of an affine open, its section-representer Ext vanishes through
degree three. -/
theorem sectionRepresenter_ext_one_two_three_subsingleton_of_isAffineOpen_of_restrict
    [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules)
    (hQC : ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent) :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 3) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let Z : Scheme.{u} := Spec R
  let j : Z ⟶ X := hU.fromSpec
  let F : X.Modules ⥤ Z.Modules := Scheme.Modules.restrictFunctor j
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : EnoughInjectives Z.Modules :=
    sheafOfModules_enoughInjectives Z.ringCatSheaf
  letI : HasExt.{u} Z.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Z.Modules
  letI : (F.obj M).IsQuasicoherent := hQC
  have h₁ : Subsingleton (schemeModuleCohomology Z (F.obj M) 1) :=
    affine_quasicoherent_cohomology_succ (R := R) (F.obj M) 0
  have h₂ : Subsingleton (schemeModuleCohomology Z (F.obj M) 2) := by
    simpa using affine_quasicoherent_cohomology_succ (R := R) (F.obj M) 1
  have h₃ : Subsingleton (schemeModuleCohomology Z (F.obj M) 3) := by
    simpa using affine_quasicoherent_cohomology_succ (R := R) (F.obj M) 2
  have h := sectionRepresenter_ext_one_two_three_subsingleton_of_restrict
    j M h₁ h₂ h₃
  simpa [j, Z, IsAffineOpen.opensRange_fromSpec] using h

/-- Quasicoherent modules have vanishing section-representer Ext through
degree three on every affine open of a locally noetherian scheme. -/
theorem sectionRepresenter_ext_one_two_three_subsingleton_of_isAffineOpen
    [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] :
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) ∧
    Subsingleton (Ext.{u}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 3) := by
  apply sectionRepresenter_ext_one_two_three_subsingleton_of_isAffineOpen_of_restrict
    U hU M
  infer_instance

end PfaffianDescent
