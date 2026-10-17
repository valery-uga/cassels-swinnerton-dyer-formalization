import PfaffianDescent.TargetAffineQuotientSheaf
import PfaffianDescent.BundleSectionZeroLocus
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! The canonical module-sheaf base-change map for a closed immersion. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The canonical pullback of the unit module is invariant under an equality
of scheme morphisms. -/
theorem pullbackUnitComparison_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
      BundleSectionZeroLocus.pullbackUnitComparison g =
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  cases h
  rfl

/-- The quotient map induced by a scheme morphism is adjoint to the
canonical map from the pulled-back unit module. -/
theorem closedImmersionUnitToPushforwardUnit_adjunct
    {X Y : Scheme.{u}} (i : X ⟶ Y) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) =
    BundleSectionZeroLocus.pullbackUnitComparison i := rfl

theorem closedImmersionUnitToPushforwardUnit_pullback_counit
    {X Y : Scheme.{u}} (i : X ⟶ Y) :
    (Scheme.Modules.pullback i).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app
        (SheafOfModules.unit X.ringCatSheaf) =
    BundleSectionZeroLocus.pullbackUnitComparison i := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction i
  calc
    (Scheme.Modules.pullback i).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
        A.counit.app (SheafOfModules.unit X.ringCatSheaf) =
      (A.homEquiv _ _).symm
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) :=
      (A.homEquiv_counit _ _ _).symm
    _ = BundleSectionZeroLocus.pullbackUnitComparison i :=
      closedImmersionUnitToPushforwardUnit_adjunct i

/-- The two routes for pulling back the structure sheaf around a fibre-product
square agree. This is the unit-module coherence needed for the quotient-map
comparison of the global base-change morphism. -/
theorem pullbackSquare_unitComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) :
    let j := pullback.fst f i
    let g := pullback.snd f i
    (Scheme.Modules.pullbackComp j f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullbackCongr
        (show j ≫ f = g ≫ i from pullback.condition)).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullbackComp g i).inv.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullback g).map
          (BundleSectionZeroLocus.pullbackUnitComparison i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison g =
    (Scheme.Modules.pullback j).map
        (BundleSectionZeroLocus.pullbackUnitComparison f) ≫
      BundleSectionZeroLocus.pullbackUnitComparison j := by
  let j := pullback.fst f i
  let g := pullback.snd f i
  have hsq : j ≫ f = g ≫ i := pullback.condition
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let t₁ := (Scheme.Modules.pullbackComp j f).hom.app O
  let t₂ := (Scheme.Modules.pullbackCongr hsq).hom.app O
  let t₃ := (Scheme.Modules.pullbackComp g i).inv.app O
  let ugi := BundleSectionZeroLocus.pullbackUnitComparison (g ≫ i)
  let ujf := BundleSectionZeroLocus.pullbackUnitComparison (j ≫ f)
  have hgi : (Scheme.Modules.pullbackComp g i).hom.app O ≫ ugi =
      (Scheme.Modules.pullback g).map
        (BundleSectionZeroLocus.pullbackUnitComparison i) ≫
        BundleSectionZeroLocus.pullbackUnitComparison g :=
    BundleSectionZeroLocus.pullbackUnitComparison_comp g i
  have hjf : t₁ ≫ ujf =
      (Scheme.Modules.pullback j).map
        (BundleSectionZeroLocus.pullbackUnitComparison f) ≫
        BundleSectionZeroLocus.pullbackUnitComparison j :=
    BundleSectionZeroLocus.pullbackUnitComparison_comp j f
  have hcongr : t₂ ≫ ugi = ujf :=
    pullbackUnitComparison_congr hsq
  have hleft : t₃ ≫ (Scheme.Modules.pullback g).map
      (BundleSectionZeroLocus.pullbackUnitComparison i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison g = ugi := by
    rw [← hgi]
    exact ((Scheme.Modules.pullbackComp g i).app O).inv_hom_id_assoc ugi
  change t₁ ≫ t₂ ≫ t₃ ≫
    (Scheme.Modules.pullback g).map
      (BundleSectionZeroLocus.pullbackUnitComparison i) ≫
    BundleSectionZeroLocus.pullbackUnitComparison g = _
  rw [hleft, hcongr]
  exact hjf

/-- The natural isomorphism between the two ways of pulling back a module
through a fibre-product square. -/
noncomputable def pullbackSquareModuleComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) :
    (Scheme.Modules.pullback f ⋙
      Scheme.Modules.pullback (pullback.fst f i)) ≅
    (Scheme.Modules.pullback i ⋙
      Scheme.Modules.pullback (pullback.snd f i)) := by
  let j := pullback.fst f i
  let g := pullback.snd f i
  have hsq : j ≫ f = g ≫ i := pullback.condition
  exact Scheme.Modules.pullbackComp j f ≪≫
    Scheme.Modules.pullbackCongr hsq ≪≫
    (Scheme.Modules.pullbackComp g i).symm

theorem pullbackSquareModuleComparison_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) :
    (pullbackSquareModuleComparison f i).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pullback (pullback.snd f i)).map
        (BundleSectionZeroLocus.pullbackUnitComparison i) ≫
      BundleSectionZeroLocus.pullbackUnitComparison (pullback.snd f i) =
    (Scheme.Modules.pullback (pullback.fst f i)).map
        (BundleSectionZeroLocus.pullbackUnitComparison f) ≫
      BundleSectionZeroLocus.pullbackUnitComparison (pullback.fst f i) := by
  exact pullbackSquare_unitComparison f i

/-- The adjoint mate of the pullback square and the counit for a closed
immersion. This is the canonical map from the pulled-back original
pushforward to the pushforward on the actual fibre product. -/
noncomputable def closedImmersionPushforwardBaseChangeHom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ⟶
    (Scheme.Modules.pushforward (pullback.fst f i)).obj
      (SheafOfModules.unit (pullback f i).ringCatSheaf) := by
  let j := pullback.fst f i
  let g := pullback.snd f i
  let M : Y.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let Pj := Scheme.Modules.pullback j
  let Pg := Scheme.Modules.pullback g
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let t : Pj.obj ((Scheme.Modules.pullback f).obj M) ⟶
      Pg.obj ((Scheme.Modules.pullback i).obj M) :=
    (pullbackSquareModuleComparison f i).hom.app M
  let t₄ : Pg.obj ((Scheme.Modules.pullback i).obj M) ⟶
      Pg.obj (SheafOfModules.unit Z.ringCatSheaf) :=
    Pg.map ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app
      (SheafOfModules.unit Z.ringCatSheaf))
  let t₅ : Pg.obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      SheafOfModules.unit (pullback f i).ringCatSheaf :=
    BundleSectionZeroLocus.pullbackUnitComparison g
  exact A.homEquiv _ _ (t ≫ t₄ ≫ t₅)

/-- The global base-change morphism intertwines the pulled-back original
quotient with the quotient of the actual fibre-product closed immersion. -/
theorem closedImmersionPushforwardBaseChangeHom_quotient
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
      closedImmersionPushforwardBaseChangeHom f i =
    BundleSectionZeroLocus.pullbackUnitComparison f ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (pullback.fst f i) := by
  let j := pullback.fst f i
  let g := pullback.snd f i
  let Pj := Scheme.Modules.pullback j
  let Pf := Scheme.Modules.pullback f
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let qj := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  let uf := BundleSectionZeroLocus.pullbackUnitComparison f
  apply ((A.homEquiv _ _).symm).injective
  change (A.homEquiv _ _).symm (Pf.map q ≫
      closedImmersionPushforwardBaseChangeHom f i) =
    (A.homEquiv _ _).symm (uf ≫ qj)
  calc
    (A.homEquiv _ _).symm (Pf.map q ≫
        closedImmersionPushforwardBaseChangeHom f i) =
      Pj.map (Pf.map q) ≫
        (A.homEquiv _ _).symm
          (closedImmersionPushforwardBaseChangeHom f i) :=
      A.homEquiv_naturality_left_symm _ _
    _ = Pj.map uf ≫ (A.homEquiv _ _).symm qj := by
      let Pg := Scheme.Modules.pullback g
      let Pi := Scheme.Modules.pullback i
      let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
      let M : Y.Modules := (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)
      let α := pullbackSquareModuleComparison f i
      let ε := (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app
        (SheafOfModules.unit Z.ringCatSheaf)
      let ug := BundleSectionZeroLocus.pullbackUnitComparison g
      let ui := BundleSectionZeroLocus.pullbackUnitComparison i
      let uj := BundleSectionZeroLocus.pullbackUnitComparison j
      have hbc : (A.homEquiv _ _).symm
          (closedImmersionPushforwardBaseChangeHom f i) =
          α.hom.app M ≫ Pg.map ε ≫ ug := by
        change (A.homEquiv _ _).symm
          ((A.homEquiv _ _) (α.hom.app M ≫ Pg.map ε ≫ ug)) = _
        exact Equiv.symm_apply_apply _ _
      have hnat : Pj.map (Pf.map q) ≫ α.hom.app M =
          α.hom.app O ≫ Pg.map (Pi.map q) :=
        α.hom.naturality q
      have hqi : Pi.map q ≫ ε = ui :=
        closedImmersionUnitToPushforwardUnit_pullback_counit i
      have hqj : (A.homEquiv _ _).symm qj = uj :=
        closedImmersionUnitToPushforwardUnit_adjunct j
      calc
        Pj.map (Pf.map q) ≫
            (A.homEquiv _ _).symm (closedImmersionPushforwardBaseChangeHom f i) =
          Pj.map (Pf.map q) ≫ (α.hom.app M ≫ Pg.map ε ≫ ug) :=
          congrArg (Pj.map (Pf.map q) ≫ ·) hbc
        _ = (α.hom.app O ≫ Pg.map (Pi.map q)) ≫ Pg.map ε ≫ ug := by
          exact congrArg (fun t => t ≫ Pg.map ε ≫ ug) hnat
        _ = α.hom.app O ≫ Pg.map ui ≫ ug := by
          have hmap : Pg.map (Pi.map q) ≫ Pg.map ε = Pg.map ui :=
            (Pg.map_comp _ _).symm.trans (congrArg Pg.map hqi)
          calc
            (α.hom.app O ≫ Pg.map (Pi.map q)) ≫ Pg.map ε ≫ ug =
                (α.hom.app O ≫
                  (Pg.map (Pi.map q) ≫ Pg.map ε)) ≫ ug :=
              congrArg (· ≫ ug) (Category.assoc _ _ _)
            _ = α.hom.app O ≫ Pg.map ui ≫ ug :=
              congrArg (fun t => (α.hom.app O ≫ t) ≫ ug) hmap
        _ = Pj.map uf ≫ uj := pullbackSquareModuleComparison_unit f i
        _ = Pj.map uf ≫ (A.homEquiv _ _).symm qj :=
          congrArg (Pj.map uf ≫ ·) hqj.symm
    _ = (A.homEquiv _ _).symm (uf ≫ qj) :=
      (A.homEquiv_naturality_left_symm _ _).symm

/-- Base change of the pushed-forward structure sheaf of a closed
immersion is always surjective as a map of module sheaves. -/
theorem closedImmersionPushforwardBaseChangeHom_epi
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    Epi (closedImmersionPushforwardBaseChangeHom f i) := by
  let j := pullback.fst f i
  let uf := BundleSectionZeroLocus.pullbackUnitComparison f
  let qj := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  have hIsoUf : IsIso uf := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  have hEpiUf : Epi uf := by
    letI := hIsoUf
    exact IsIso.epi_of_iso uf
  have hEpiQj : Epi qj := by
    dsimp only [qj]
    infer_instance
  haveI : Epi (uf ≫ qj) := epi_comp' hEpiUf hEpiQj
  exact epi_of_epi_fac (closedImmersionPushforwardBaseChangeHom_quotient f i)

/-- The induced map between the two quotient kernels in the base-change
square. Its invertibility is the precise remaining ideal-comparison
obligation. -/
noncomputable def closedImmersionPushforwardBaseChangeKernelMap
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    kernel ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) ⟶
    kernel (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (pullback.fst f i)) :=
  kernel.map _ _
    (BundleSectionZeroLocus.pullbackUnitComparison f)
    (closedImmersionPushforwardBaseChangeHom f i)
    (closedImmersionPushforwardBaseChangeHom_quotient f i)

theorem closedImmersionPushforwardBaseChangeKernelMap_comp_ι
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    closedImmersionPushforwardBaseChangeKernelMap f i ≫
      kernel.ι (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (pullback.fst f i)) =
      kernel.ι ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) ≫
      BundleSectionZeroLocus.pullbackUnitComparison f := by
  exact kernel.lift_ι _ _ _

/-- Once the geometric map on ideal kernels is an isomorphism, the global
pushforward base-change map is monic. This is the short-five-lemma step. -/
theorem closedImmersionPushforwardBaseChangeHom_mono_of_kernelMap_isIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionPushforwardBaseChangeKernelMap f i)] :
    Mono (closedImmersionPushforwardBaseChangeHom f i) := by
  let P := Scheme.Modules.pullback f
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let j := pullback.fst f i
  let qj := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  let uf := BundleSectionZeroLocus.pullbackUnitComparison f
  let b := closedImmersionPushforwardBaseChangeHom f i
  let k := closedImmersionPushforwardBaseChangeKernelMap f i
  let S₁ := ShortComplex.kernelSequence (P.map q)
  let S₂ := ShortComplex.kernelSequence qj
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk k uf b
    (closedImmersionPushforwardBaseChangeKernelMap_comp_ι f i)
    (closedImmersionPushforwardBaseChangeHom_quotient f i).symm
  have h₂ : S₂.Exact := ShortComplex.kernelSequence_exact qj
  have hq : Epi q := by
    dsimp only [q]
    infer_instance
  have hqP : Epi (P.map q) := @Functor.map_epi _ _ _ _ P _ _ _ q hq
  have hg₁ : Epi S₁.g := hqP
  have hk : Epi φ.τ₁ := by
    change Epi k
    infer_instance
  have hu : Mono φ.τ₂ := by
    change Mono uf
    haveI : IsIso uf := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
    exact IsIso.mono_of_iso uf
  exact ShortComplex.mono_of_epi_of_epi_of_mono φ h₂ hg₁ hk hu

/-- The global base-change map is an isomorphism as soon as the induced
geometric ideal-kernel map is an isomorphism. -/
theorem closedImmersionPushforwardBaseChangeHom_isIso_of_kernelMap_isIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [IsIso (closedImmersionPushforwardBaseChangeKernelMap f i)] :
    IsIso (closedImmersionPushforwardBaseChangeHom f i) := by
  haveI : Mono (closedImmersionPushforwardBaseChangeHom f i) :=
    closedImmersionPushforwardBaseChangeHom_mono_of_kernelMap_isIso f i
  haveI : Epi (closedImmersionPushforwardBaseChangeHom f i) :=
    closedImmersionPushforwardBaseChangeHom_epi f i
  exact isIso_of_mono_of_epi _

/-- A morphism from the pulled-back closed-immersion pushforward is uniquely
determined by its composite with the pulled-back quotient map. This also
supplies uniqueness for the canonical base-change map once its quotient
compatibility is shown. -/
theorem closedImmersionPushforwardBaseChangeHom_unique
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (h₁ h₂ :
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⟶
      (Scheme.Modules.pushforward (pullback.fst f i)).obj
        (SheafOfModules.unit (pullback f i).ringCatSheaf))
    (h₁q : (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ h₁ =
      BundleSectionZeroLocus.pullbackUnitComparison f ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (pullback.fst f i))
    (h₂q : (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ h₂ =
      BundleSectionZeroLocus.pullbackUnitComparison f ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (pullback.fst f i)) :
    h₁ = h₂ := by
  let P := Scheme.Modules.pullback f
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  have hq : Epi q := by
    dsimp only [q]
    infer_instance
  haveI : Epi (P.map q) := @Functor.map_epi _ _ _ _ P _ _ _ q hq
  apply (cancel_epi (P.map q)).mp
  exact h₁q.trans h₂q.symm

end PfaffianDescent
