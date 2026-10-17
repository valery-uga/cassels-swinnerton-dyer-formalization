import PfaffianDescent.SchemeModuleRankOneDualKernelIso
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! The SAME dual kernel contraction carries the SAME original inclusion
to tensoring the SAME canonical increment. The comparison/unit identities
are proved from original raw evaluation and actual sheafification triangles.
No desired action/comparison square is an input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- The literal tensor of the SAME original dual increment, with its
actual right-unitor source identification. -/
def schemeModuleRankOneTensorDualIncrement {M : X.Modules}
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (L : X.Modules) :
    L ⟶ schemeModuleTensor L (SchemeModuleInternalHom.dual M) :=
  (schemeModuleTensorUnitRightIso L).inv ≫
    schemeModuleTensorMap (𝟙 L) (SchemeModuleInternalHom.unitToHom j)

/-- The new first map is exactly the SAME original increment tensored
on the right by L, with actual unit and symmetry comparisons. -/
theorem schemeModuleRankOneTensorDualIncrement_eq_rightTensor
    {M : X.Modules} (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (L : X.Modules) :
    schemeModuleRankOneTensorDualIncrement j L =
      (schemeModuleTensorUnitLeftIso L).inv ≫
        schemeModuleTensorMap (SchemeModuleInternalHom.unitToHom j) (𝟙 L) ≫
        (schemeModuleTensorSymmetry (SchemeModuleInternalHom.dual M) L).hom := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let D : X.Modules := SchemeModuleInternalHom.dual M
  let delta : O ⟶ D := SchemeModuleInternalHom.unitToHom j
  let b : schemeModuleTensor L O ≅ schemeModuleTensor O L := schemeModuleTensorSymmetry L O
  let bO : schemeModuleTensor O L ≅ schemeModuleTensor L O := schemeModuleTensorSymmetry O L
  let bD : schemeModuleTensor D L ≅ schemeModuleTensor L D := schemeModuleTensorSymmetry D L
  let l : schemeModuleTensor O L ≅ L := schemeModuleTensorUnitLeftIso L
  let r : schemeModuleTensor L O ≅ L := schemeModuleTensorUnitRightIso L
  have he : b ≪≫ l = r := Iso.ext (schemeModuleTensorSymmetry_unit_leftUnitor L)
  have hu : l.inv ≫ bO.hom = r.inv := by
    have h := congrArg (fun e : schemeModuleTensor L O ≅ L => e.inv) he
    change l.inv ≫ b.inv = r.inv at h
    exact (congrArg (fun v : schemeModuleTensor O L ⟶ schemeModuleTensor L O => l.inv ≫ v)
      (schemeModuleTensorSymmetry_inv_eq L O)).symm.trans h
  have hn : schemeModuleTensorMap delta (𝟙 L) ≫ bD.hom =
      bO.hom ≫ schemeModuleTensorMap (𝟙 L) delta :=
    schemeModuleTensorSymmetry_naturality delta (𝟙 L)
  change r.inv ≫ schemeModuleTensorMap (𝟙 L) delta =
    l.inv ≫ schemeModuleTensorMap delta (𝟙 L) ≫ bD.hom
  symm
  calc
    _ = l.inv ≫ bO.hom ≫ schemeModuleTensorMap (𝟙 L) delta := by
      simpa only [Category.assoc] using
        congrArg (fun v : schemeModuleTensor O L ⟶ schemeModuleTensor L D => l.inv ≫ v) hn
    _ = r.inv ≫ schemeModuleTensorMap (𝟙 L) delta := by
      simpa only [Category.assoc] using
        congrArg (fun v : L ⟶ schemeModuleTensor L O => v ≫ schemeModuleTensorMap (𝟙 L) delta) hu

/-- SAME swapped raw evaluation followed by SAME delta is the literal
original inclusion coefficient acting on the original dual factor. -/
theorem schemeModuleRankOneSwappedPairingRaw_action
    {M : X.Modules} (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hM : schemeModuleLocallyRankOne M) :
    schemeModuleTensorPairingRaw (SchemeModuleInternalHom.dual M) M
        (schemeModuleRankOneSwappedDualPairingIso M hM) ≫
      (SchemeModuleInternalHom.unitToHom j).val =
    PresheafOfModules.Monoidal.tensorHom (𝟙 (SchemeModuleInternalHom.dual M).val) j.val ≫
      (schemeModuleTensorUnitRightRawIso (SchemeModuleInternalHom.dual M)).hom := by
  classical
  let R : X.Opensᵒᵖ ⥤ CommRingCat := X.sheaf.obj
  let A : X.Opensᵒᵖ ⥤ RingCat := R ⋙ forget₂ CommRingCat RingCat
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let D : X.Modules := SchemeModuleInternalHom.dual M
  let m : PresheafOfModules A := M.val
  let d : PresheafOfModules A := D.val
  let o : PresheafOfModules A := PresheafOfModules.unit A
  let j₀ : m ⟶ o := j.val
  let delta : o ⟶ d := (SchemeModuleInternalHom.unitToHom j).val
  let E : PresheafOfModules.Monoidal.tensorObj m d ⟶ o :=
    SchemeModuleInternalHom.evaluationPresheaf M O
  let pair : PresheafOfModules.Monoidal.tensorObj d m ⟶ o :=
    schemeModuleTensorPairingRaw D M (schemeModuleRankOneSwappedDualPairingIso M hM)
  letI : MonoidalCategory (PresheafOfModules A) := PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules A) := PresheafOfModules.symmetricCategory
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  have he : E ≫ delta = (j₀ ⊗ₘ (𝟙 d)) ≫ (λ_ d).hom := by
    have h := SchemeModuleInternalHom.rankOneEvaluation_presheaf_action_of_pointwise_unitCharts
      j B hB eB
    change E ≫ delta = (j₀ ⊗ₘ (𝟙 d)) ≫ (λ_ d).hom at h
    exact h
  have hp : pair = (β_ d m).hom ≫ E := schemeModuleRankOneSwappedDualPairingRaw M hM
  have hb : ((𝟙 d) ⊗ₘ j₀) ≫ (β_ d o).hom = (β_ d m).hom ≫ (j₀ ⊗ₘ (𝟙 d)) :=
    BraidedCategory.braiding_naturality (𝟙 d) j₀
  have hu : (β_ d o).hom ≫ (λ_ d).hom = (ρ_ d).hom :=
    CategoryTheory.braiding_leftUnitor d
  change pair ≫ delta = ((𝟙 d) ⊗ₘ j₀) ≫ (ρ_ d).hom
  calc
    _ = ((β_ d m).hom ≫ E) ≫ delta := congrArg (fun v => v ≫ delta) hp
    _ = (β_ d m).hom ≫ (E ≫ delta) := Category.assoc _ _ _
    _ = (β_ d m).hom ≫ ((j₀ ⊗ₘ (𝟙 d)) ≫ (λ_ d).hom) :=
      congrArg (fun v : m ⊗ d ⟶ d => (β_ d m).hom ≫ v) he
    _ = ((β_ d m).hom ≫ (j₀ ⊗ₘ (𝟙 d))) ≫ (λ_ d).hom :=
      (Category.assoc _ _ _).symm
    _ = (((𝟙 d) ⊗ₘ j₀) ≫ (β_ d o).hom) ≫ (λ_ d).hom :=
      congrArg (fun v : d ⊗ m ⟶ o ⊗ d => v ≫ (λ_ d).hom) hb.symm
    _ = ((𝟙 d) ⊗ₘ j₀) ≫ ((β_ d o).hom ≫ (λ_ d).hom) := Category.assoc _ _ _
    _ = ((𝟙 d) ⊗ₘ j₀) ≫ (ρ_ d).hom :=
      congrArg (fun v : d ⊗ o ⟶ d => ((𝟙 d) ⊗ₘ j₀) ≫ v) hu

/-- The actual raw triple-tensor action. This is the genuine associator
naturality/unit identity applied to the preceding SAME evaluation square. -/
theorem schemeModuleRankOneDualKernel_raw_action
    {M : X.Modules} (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (L : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    let D := SchemeModuleInternalHom.dual M
    let P := PresheafOfModules.Monoidal.tensorObj L.val D.val
    (α_ L.val D.val M.val).hom ≫
      PresheafOfModules.Monoidal.tensorHom (𝟙 L.val)
        (schemeModuleTensorPairingRaw D M (schemeModuleRankOneSwappedDualPairingIso M hM) ≫
          (SchemeModuleInternalHom.unitToHom j).val) =
      PresheafOfModules.Monoidal.tensorHom (𝟙 P) j.val ≫ (ρ_ P).hom := by
  let R : X.Opensᵒᵖ ⥤ CommRingCat := X.sheaf.obj
  let A : X.Opensᵒᵖ ⥤ RingCat := R ⋙ forget₂ CommRingCat RingCat
  let D : X.Modules := SchemeModuleInternalHom.dual M
  let l : PresheafOfModules A := L.val
  let d : PresheafOfModules A := D.val
  let m : PresheafOfModules A := M.val
  let o : PresheafOfModules A := PresheafOfModules.unit A
  let P : PresheafOfModules A := PresheafOfModules.Monoidal.tensorObj (R := R) l d
  let j₀ : m ⟶ o := j.val
  let delta : o ⟶ d := (SchemeModuleInternalHom.unitToHom j).val
  let pair : PresheafOfModules.Monoidal.tensorObj d m ⟶ o :=
    schemeModuleTensorPairingRaw D M (schemeModuleRankOneSwappedDualPairingIso M hM)
  letI : MonoidalCategory (PresheafOfModules A) := PresheafOfModules.monoidalCategory (R := R)
  have hP : P = l ⊗ d := rfl
  let b : d ⊗ m ⟶ d ⊗ o := (𝟙 d) ⊗ₘ j₀
  let r : d ⊗ o ⟶ d := (ρ_ d).hom
  have hp : pair ≫ delta = b ≫ r := schemeModuleRankOneSwappedPairingRaw_action j hM
  have hs : ((𝟙 l) ⊗ₘ (b ≫ r)) = ((𝟙 l) ⊗ₘ b) ≫ ((𝟙 l) ⊗ₘ r) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (𝟙 l) b (𝟙 l) r).symm
  have hn : ((𝟙 P) ⊗ₘ j₀) ≫ (α_ l d o).hom =
      (α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ b) := by
    dsimp only [P]
    change ((𝟙 (l ⊗ d)) ⊗ₘ j₀) ≫ (α_ l d o).hom =
      (α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ b)
    simpa only [b, id_tensorHom_id] using associator_naturality (𝟙 l) (𝟙 d) j₀
  have hu : (α_ l d o).hom ≫ ((𝟙 l) ⊗ₘ r) = (ρ_ P).hom :=
    (rightUnitor_tensor_hom l d).symm
  change (α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ (pair ≫ delta)) = ((𝟙 P) ⊗ₘ j₀) ≫ (ρ_ P).hom
  calc
    _ = (α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ (b ≫ r)) :=
      congrArg (fun v : d ⊗ m ⟶ d => (α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ v)) hp
    _ = (α_ l d m).hom ≫ (((𝟙 l) ⊗ₘ b) ≫ ((𝟙 l) ⊗ₘ r)) :=
      congrArg (fun v => (α_ l d m).hom ≫ v) hs
    _ = ((α_ l d m).hom ≫ ((𝟙 l) ⊗ₘ b)) ≫ ((𝟙 l) ⊗ₘ r) :=
      (Category.assoc _ _ _).symm
    _ = (((𝟙 P) ⊗ₘ j₀) ≫ (α_ l d o).hom) ≫ ((𝟙 l) ⊗ₘ r) :=
      congrArg (fun v : P ⊗ m ⟶ l ⊗ (d ⊗ o) => v ≫ ((𝟙 l) ⊗ₘ r)) hn.symm
    _ = ((𝟙 P) ⊗ₘ j₀) ≫ ((α_ l d o).hom ≫ ((𝟙 l) ⊗ₘ r)) := Category.assoc _ _ _
    _ = ((𝟙 P) ⊗ₘ j₀) ≫ (ρ_ P).hom :=
      congrArg (fun v : P ⊗ o ⟶ P => ((𝟙 P) ⊗ₘ j₀) ≫ v) hu

/-- The required GLOBAL canonical kernel/inclusion square. Both original
sheafification steps remain explicit. Cancellation uses the internally
invertible comparison; no desired compatibility is assumed. -/
theorem schemeModuleRankOneDualKernelIso_action
    {M : X.Modules} (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (L : X.Modules) (hM : schemeModuleLocallyRankOne M) :
    (schemeModuleRankOneDualKernelIso M L hM).hom ≫
      schemeModuleRankOneTensorDualIncrement j L =
    schemeModuleTensorMap j (𝟙 (schemeModuleTensor L (SchemeModuleInternalHom.dual M))) ≫
      (schemeModuleTensorUnitLeftIso (schemeModuleTensor L (SchemeModuleInternalHom.dual M))).hom := by
  let R : X.Opensᵒᵖ ⥤ CommRingCat := X.sheaf.obj
  let A : X.Opensᵒᵖ ⥤ RingCat := R ⋙ forget₂ CommRingCat RingCat
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let D : X.Modules := SchemeModuleInternalHom.dual M
  let l : PresheafOfModules A := L.val
  let d₀ : PresheafOfModules A := D.val
  let m : PresheafOfModules A := M.val
  let o : PresheafOfModules A := PresheafOfModules.unit A
  let P : PresheafOfModules A := PresheafOfModules.Monoidal.tensorObj l d₀
  let T : X.Modules := schemeModuleTensor L D
  let F : PresheafOfModules A ⥤ X.Modules := PresheafOfModules.sheafification (𝟙 A)
  let G : X.Modules ⥤ PresheafOfModules A :=
    SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.restrictScalars (𝟙 A)
  let adj : F ⊣ G :=
    PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (R₀ := A) (𝟙 A)
  let e : schemeModuleTensor D M ≅ O := schemeModuleRankOneSwappedDualPairingIso M hM
  let C : F.obj (PresheafOfModules.Monoidal.tensorObj P m) ⟶ schemeModuleTensor T M :=
    schemeModuleTensorSheafificationRightComparison P M
  let C₀ : F.obj (PresheafOfModules.Monoidal.tensorObj P o) ⟶ schemeModuleTensor T O :=
    schemeModuleTensorSheafificationRightComparison P O
  let s : schemeModuleTensor M T ≅ schemeModuleTensor T M := schemeModuleTensorSymmetry M T
  let pair : PresheafOfModules.Monoidal.tensorObj d₀ m ⟶ o := schemeModuleTensorPairingRaw D M e
  let delta : O ⟶ D := SchemeModuleInternalHom.unitToHom j
  let delta₀ : o ⟶ d₀ := delta.val
  let j₀ : m ⟶ o := j.val
  letI : MonoidalCategory (PresheafOfModules A) := PresheafOfModules.monoidalCategory
  letI : IsIso C := schemeModuleLocallyRankOne_rightComparison_isIso P M hM
  let a : P ⊗ m ⟶ l ⊗ (d₀ ⊗ m) := (α_ l d₀ m).hom
  let t : l ⊗ (d₀ ⊗ m) ⟶ l ⊗ o := (𝟙 l) ⊗ₘ pair
  let r : l ⊗ o ⟶ l := (ρ_ l).hom
  let d : l ⊗ o ⟶ P := (𝟙 l) ⊗ₘ delta₀
  let g : P ⊗ m ⟶ P ⊗ o := (𝟙 P) ⊗ₘ j₀
  let rP : P ⊗ o ⟶ P := (ρ_ P).hom
  let rL : schemeModuleTensor L O ≅ L := schemeModuleTensorUnitRightIso L
  let rT : schemeModuleTensor T O ≅ T := schemeModuleTensorUnitRightIso T
  let lT : schemeModuleTensor O T ≅ T := schemeModuleTensorUnitLeftIso T
  let bO : schemeModuleTensor T O ≅ schemeModuleTensor O T := schemeModuleTensorSymmetry T O
  let K : schemeModuleTensor M T ≅ L := schemeModuleRankOneDualKernelIso M L hM
  let deltaL : L ⟶ T := schemeModuleRankOneTensorDualIncrement j L
  let v : schemeModuleTensor M T ⟶ schemeModuleTensor O T := schemeModuleTensorMap j (𝟙 T)
  let w : schemeModuleTensor T M ⟶ schemeModuleTensor T O := schemeModuleTensorMap (𝟙 T) j
  have hd : schemeModuleTensorMap (𝟙 L) delta = F.map d :=
    schemeModuleTensorMap_eq_sheafification (𝟙 L) delta
  have hdelta : deltaL = rL.inv ≫ F.map d :=
    congrArg (fun z : schemeModuleTensor L O ⟶ T => rL.inv ≫ z) hd
  have hK : (C ≫ s.inv) ≫ K.hom = F.map a ≫ F.map t ≫ F.map r ≫ adj.counit.app L := by
    change C ≫ s.inv ≫ (s.hom ≫ inv C ≫ F.map a ≫ F.map t ≫
      F.map r ≫ adj.counit.app L) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]
  have hU : (F.map r ≫ adj.counit.app L) ≫ rL.inv = 𝟙 (schemeModuleTensor L O) := by
    change rL.hom ≫ rL.inv = _
    exact rL.hom_inv_id
  have htd : t ≫ d = (𝟙 l) ⊗ₘ (pair ≫ delta₀) := by
    simpa only [Category.id_comp] using tensorHom_comp_tensorHom (𝟙 l) pair (𝟙 l) delta₀
  have hraw : a ≫ ((𝟙 l) ⊗ₘ (pair ≫ delta₀)) = g ≫ rP :=
    schemeModuleRankOneDualKernel_raw_action j L hM
  have hleft : ((C ≫ s.inv) ≫ K.hom) ≫ deltaL = F.map (g ≫ rP) := by
    rw [hK, hdelta]
    calc
      _ = (F.map a ≫ F.map t) ≫ ((F.map r ≫ adj.counit.app L) ≫ rL.inv) ≫ F.map d := by
        simp only [Category.assoc]
      _ = (F.map a ≫ F.map t) ≫ (𝟙 (schemeModuleTensor L O)) ≫ F.map d :=
        congrArg (fun z : schemeModuleTensor L O ⟶ schemeModuleTensor L O =>
          (F.map a ≫ F.map t) ≫ z ≫ F.map d) hU
      _ = (F.map a ≫ F.map t) ≫ F.map d :=
        congrArg (fun z : schemeModuleTensor L O ⟶ T => (F.map a ≫ F.map t) ≫ z)
          (Category.id_comp (F.map d))
      _ = F.map (a ≫ (t ≫ d)) := by simp only [F.map_comp, Category.assoc]
      _ = F.map (a ≫ ((𝟙 l) ⊗ₘ (pair ≫ delta₀))) :=
        congrArg (fun z : l ⊗ (d₀ ⊗ m) ⟶ P => F.map (a ≫ z)) htd
      _ = F.map (g ≫ rP) := congrArg F.map hraw
  have hn : w ≫ bO.hom = s.inv ≫ v := by
    have h := schemeModuleTensorSymmetry_naturality (𝟙 T) j
    change w ≫ bO.hom = (schemeModuleTensorSymmetry T M).hom ≫ v at h
    exact h.trans (congrArg (fun z : schemeModuleTensor T M ⟶ schemeModuleTensor M T => z ≫ v)
      (schemeModuleTensorSymmetry_inv_eq M T)).symm
  have hs : bO.hom ≫ lT.hom = rT.hom := schemeModuleTensorSymmetry_unit_leftUnitor T
  have hc : C ≫ w = F.map g ≫ C₀ := schemeModuleTensorSheafificationRightComparison_naturality P j
  have hnorm : C₀ ≫ rT.hom = F.map rP := schemeModuleTensorRightComparison_unit_normalization P
  have hright : (C ≫ s.inv) ≫ (v ≫ lT.hom) = F.map (g ≫ rP) := by
    calc
      _ = C ≫ (s.inv ≫ v) ≫ lT.hom := by simp only [Category.assoc]
      _ = C ≫ (w ≫ bO.hom) ≫ lT.hom :=
        congrArg (fun z : schemeModuleTensor T M ⟶ schemeModuleTensor O T => C ≫ z ≫ lT.hom) hn.symm
      _ = (C ≫ w) ≫ (bO.hom ≫ lT.hom) := by simp only [Category.assoc]
      _ = (C ≫ w) ≫ rT.hom :=
        congrArg (fun z : schemeModuleTensor T O ⟶ T => (C ≫ w) ≫ z) hs
      _ = (F.map g ≫ C₀) ≫ rT.hom :=
        congrArg (fun z : F.obj (P ⊗ m) ⟶ schemeModuleTensor T O => z ≫ rT.hom) hc
      _ = F.map g ≫ (C₀ ≫ rT.hom) := Category.assoc _ _ _
      _ = F.map g ≫ F.map rP :=
        congrArg (fun z : F.obj (P ⊗ o) ⟶ T => F.map g ≫ z) hnorm
      _ = F.map (g ≫ rP) := (F.map_comp _ _).symm
  change K.hom ≫ deltaL = v ≫ lT.hom
  apply (cancel_epi (C ≫ s.inv)).mp
  exact (Category.assoc (C ≫ s.inv) K.hom deltaL).symm.trans (hleft.trans hright.symm)

/-- SAME original pi-induced scalar compatibility of the actual kernel Iso.
No scalar action is transported through the kernel identification. -/
theorem schemeModuleRankOneDualKernelIso_originalBaseConstant
    {K : Type u} [Field K] (pi : X ⟶ Spec (CommRingCat.of K))
    (M L : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (U : X.Opens) (c : K)
    (s : (schemeModuleTensor M (schemeModuleTensor L (SchemeModuleInternalHom.dual M))).val.obj (op U)) :
    (schemeModuleRankOneDualKernelIso M L hM).hom.val.app (op U)
        (schemeOpenBaseRingHom pi U c • s) =
      schemeOpenBaseRingHom pi U c •
        (schemeModuleRankOneDualKernelIso M L hM).hom.val.app (op U) s :=
  ((schemeModuleRankOneDualKernelIso M L hM).hom.val.app (op U)).hom.map_smul
    (schemeOpenBaseRingHom pi U c) s

end PfaffianDescent
