import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.ResidueField

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace BundleSectionZeroLocus

/-! The zero locus of a section of a globally trivial module is the closed
subscheme defined by its scalar coordinates.  This is the affine-chart piece
needed to turn the sections of Voisin's rank-two Serre pencil into
scheme-theoretic zero loci.  Compatibility of these ideals under transitions
between local trivializations is established separately. -/

variable {X : Scheme.{u}}

/-- Every equation in the top affine ideal of an ideal-sheaf subscheme
vanishes after evaluation in the residue field of each point of that
subscheme. -/
theorem idealSheafSubscheme_Γevaluation_eq_zero
    [AlgebraicGeometry.IsAffine X]
    (J : Scheme.IdealSheafData X) (y : J.subscheme)
    (f : Γ(X, ⊤))
    (hf : f ∈ J.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩) :
    X.Γevaluation (J.subschemeι y) f = 0 := by
  have hy : J.subschemeι y ∈ J.support := by
    change J.subschemeι y ∈ (J.support : Set X)
    rw [← J.range_subschemeι]
    exact ⟨y, rfl⟩
  have hz : J.subschemeι y ∈
      X.zeroLocus (U := (⊤ : X.Opens))
        (J.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩) :=
    (J.mem_support_iff_of_mem (U :=
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩) trivial).mp hy
  have hnot : J.subschemeι y ∉ X.basicOpen f :=
    (X.mem_zeroLocus_iff _ _).mp hz f hf
  let hx : J.subschemeι y ∈ (⊤ : X.Opens) := Set.mem_univ _
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen
    (J.subschemeι y) hx f).mpr hnot

/-- The canonical comparison from the pullback of the unit module to the
unit module on the source scheme.  It is named separately because its generic
construction is parameterized by a right-adjoint witness, while scheme
morphisms provide that witness canonically. -/
noncomputable def pullbackUnitComparison {Y : Scheme.{u}} (f : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- Inverse image on open subsets is a final functor.  It preserves the
terminal open subset, and any functor between categories with terminal
objects that preserves the terminal object is final. -/
theorem opensMap_final {Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let _ : PreservesLimit
      (Functor.empty.{0} Y.Opens) (TopologicalSpace.Opens.map f.base) := by
    apply CategoryTheory.Limits.preservesTerminal_of_iso
    exact (TopologicalSpace.Opens.map f.base).mapIso
        (terminalIsTerminal.uniqueUpToIso isTerminalTop) ≪≫
      eqToIso (TopologicalSpace.Opens.map_top f.base) ≪≫
      isTerminalTop.uniqueUpToIso terminalIsTerminal
  infer_instance

/-- Pullback along every scheme morphism carries the unit module to the unit
module.  The usual comparison is invertible because inverse image on opens
is final. -/
theorem isIso_pullbackUnitComparison {Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pullbackUnitComparison f) := by
  let _ : (TopologicalSpace.Opens.map f.base).Final := opensMap_final f
  let _ : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  change IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  exact SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom

/-- For an open scheme morphism, pullback preserves the unit module.  The
underlying functor on opens is a right adjoint to direct image of opens, hence
final; Mathlib's free-sheaf pullback theorem then makes the canonical unit
comparison invertible. -/
theorem isIso_pullbackUnitComparison_of_isOpenMap {Y : Scheme.{u}} (f : X ⟶ Y)
    (_hf : IsOpenMap f) : IsIso (pullbackUnitComparison f) := by
  exact isIso_pullbackUnitComparison f

/-- A finite free presentation remains a literal finite free presentation
after pullback along an arbitrary scheme morphism.  Inverse image on opens is
final for every scheme morphism, so no openness hypothesis is needed. -/
noncomputable def pullbackFreeIso {Y : Scheme.{u}} (f : X ⟶ Y)
    {E : Y.Modules} (I : Type u)
    (t : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj E := by
  letI : (TopologicalSpace.Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso t

/-- A finite free presentation remains a literal finite free presentation
after pullback along an open scheme morphism.  This packages the finality
argument for pullback of free modules together with the given
trivialization. -/
noncomputable def pullbackFreeIsoOf_isOpenMap {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsOpenMap f) {E : Y.Modules} (I : Type u)
    (t : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj E := by
  letI : (TopologicalSpace.Opens.map f.base).IsRightAdjoint :=
    (IsOpenMap.adjunction hf).isRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso t

/-- Pull a module section back along a scheme morphism whenever the canonical
comparison from the pulled-back unit module is invertible.  The comparison is
an isomorphism for the usual geometric inverse-image construction; keeping it
explicit here isolates the one sheaf-theoretic fact needed to turn the local
Serre-pencil sections into sections on a parameter-space chart. -/
noncomputable def pullbackSection {Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hunit : IsIso (pullbackUnitComparison f))
    (s : M.sections) : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).sections := by
  let backwards := Classical.choose hunit.out
  exact ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).unitHomEquiv
    (backwards ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s))

/-- The representing morphism of a pulled-back section is the pullback of
the original representing morphism, precomposed with the inverse unit
comparison. -/
theorem pullbackSection_unitHomEquiv_symm {Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hunit : IsIso (pullbackUnitComparison f))
    (s : M.sections) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
      (pullbackSection f M hunit s) =
      Classical.choose hunit.out ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s) := by
  unfold pullbackSection
  rw [Equiv.symm_apply_apply]
  congr 1

/-- When the unit comparison is invertible, the morphism representing a
pulled-back section uses its canonical categorical inverse.  This removes the
choice in `pullbackSection` from subsequent functoriality arguments. -/
theorem pullbackSection_unitHomEquiv_symm_eq_inv {Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hunit : IsIso (pullbackUnitComparison f))
    (s : M.sections) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
      (pullbackSection f M hunit s) =
      inv (pullbackUnitComparison f) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  rw [pullbackSection_unitHomEquiv_symm]
  congr 1

/-- Pullback of sections commutes with every map of module sheaves. -/
theorem sectionsMap_pullbackSection {Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N)
    (hunit : IsIso (pullbackUnitComparison f)) (s : M.sections) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map φ)
      (pullbackSection f M hunit s) =
      pullbackSection f N hunit (SheafOfModules.sectionsMap φ s) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  apply ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).unitHomEquiv.symm.injective
  rw [← (SheafOfModules.unitHomEquiv_symm_comp
    (pullbackSection f M hunit s)
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map φ))]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  erw [Category.assoc]
  erw [← Functor.map_comp (AlgebraicGeometry.Scheme.Modules.pullback f)]
  exact congrArg (fun t => inv (pullbackUnitComparison f) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).map t)
    (M.unitHomEquiv_symm_comp s φ)

/-- Pulling a section back is invariant under replacing the scheme map by an
equal map.  The equality is expressed through Mathlib's canonical
`pullbackCongr` transport, so it is usable in dependent overlap arguments. -/
theorem sectionsMap_pullbackCongr_pullbackSection {Y : Scheme.{u}}
    (f g : X ⟶ Y) (h : f = g) (M : Y.Modules)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g)) (s : M.sections) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).hom.app M)
      (pullbackSection f M hf s) =
    pullbackSection g M hg s := by
  subst g
  rfl

/-- A unit-comparison compatibility identifies iterated pullback of a section
with pullback along the composite.  The compatibility is isolated explicitly:
it is the only coherence needed to transport local pencil equations from a
chart to an overlap. -/
theorem pullbackSection_comp_of_unitComparison
    {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g))
    (hfg : IsIso (pullbackUnitComparison (f ≫ g)))
    (s : M.sections)
    (hunit :
      inv (pullbackUnitComparison (f ≫ g)) ≫
          (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app
            (SheafOfModules.unit Z.ringCatSheaf) =
        inv (pullbackUnitComparison f) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback f).map
            (inv (pullbackUnitComparison g))) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M)
      (pullbackSection (f ≫ g) M hfg s) =
    pullbackSection f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
      (pullbackSection g M hg s) := by
  letI : IsIso (pullbackUnitComparison f) := hf
  letI : IsIso (pullbackUnitComparison g) := hg
  letI : IsIso (pullbackUnitComparison (f ≫ g)) := hfg
  apply ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).unitHomEquiv.symm.injective
  erw [← (SheafOfModules.unitHomEquiv_symm_comp
    (pullbackSection (f ≫ g) M hfg s)
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M))]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  erw [Category.assoc]
  erw [(AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.naturality]
  erw [← Category.assoc]
  erw [hunit]
  change (inv (pullbackUnitComparison f) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
        (inv (pullbackUnitComparison g))) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
        ((AlgebraicGeometry.Scheme.Modules.pullback g).map
          (M.unitHomEquiv.symm s)) = _
  erw [Category.assoc]
  erw [← Functor.map_comp (AlgebraicGeometry.Scheme.Modules.pullback f)]

/-- The unit-to-pushforward comparison is compatible with composition of
scheme morphisms. -/
theorem unitToPushforwardObjUnit_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit X.ringCatSheaf) := by
  ext U
  rfl

/-- The inverse form of a comparison of pullback units.  This is the
coherence identity needed to identify an iterated restriction of a section
with restriction along the composite map. -/
theorem pullbackUnitComparison_inverse_comp_of_comp
    {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g))
    (hfg : IsIso (pullbackUnitComparison (f ≫ g)))
    (h :
      (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app
          (SheafOfModules.unit Z.ringCatSheaf) ≫
        pullbackUnitComparison (f ≫ g) =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
        (pullbackUnitComparison g) ≫ pullbackUnitComparison f) :
    inv (pullbackUnitComparison (f ≫ g)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app
          (SheafOfModules.unit Z.ringCatSheaf) =
      inv (pullbackUnitComparison f) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (inv (pullbackUnitComparison g)) := by
  letI : IsIso (pullbackUnitComparison f) := hf
  letI : IsIso (pullbackUnitComparison g) := hg
  letI : IsIso (pullbackUnitComparison (f ≫ g)) := hfg
  let E := AlgebraicGeometry.Scheme.Modules.pullbackComp f g
  letI : IsIso (E.hom.app (SheafOfModules.unit Z.ringCatSheaf)) :=
    NatIso.hom_app_isIso E _
  letI : IsIso ((AlgebraicGeometry.Scheme.Modules.pullback f).map
      (pullbackUnitComparison g)) := Functor.map_isIso _ _
  letI : IsIso (E.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      pullbackUnitComparison (f ≫ g)) := IsIso.comp_isIso
  have hleft :
      (E.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        pullbackUnitComparison (f ≫ g)) ≫
          (inv (pullbackUnitComparison (f ≫ g)) ≫
            E.inv.app (SheafOfModules.unit Z.ringCatSheaf)) = 𝟙 _ := by
    calc
      (E.hom.app _ ≫ pullbackUnitComparison (f ≫ g)) ≫
          (inv (pullbackUnitComparison (f ≫ g)) ≫ E.inv.app _) =
        E.hom.app _ ≫
          ((pullbackUnitComparison (f ≫ g) ≫
            inv (pullbackUnitComparison (f ≫ g))) ≫ E.inv.app _) := by
          exact (Category.assoc _ _ _).trans
            (congrArg (fun q => E.hom.app _ ≫ q)
              (Category.assoc _ _ _).symm)
      _ = E.hom.app _ ≫ (𝟙 _ ≫ E.inv.app _) := by
          exact congrArg (fun q => E.hom.app _ ≫ (q ≫ E.inv.app _))
            (IsIso.hom_inv_id _)
      _ = E.hom.app _ ≫ E.inv.app _ :=
        congrArg (fun q => E.hom.app _ ≫ q) (Category.id_comp _)
      _ = 𝟙 _ := E.hom_inv_id_app _
  have hleft_inv :
      inv (pullbackUnitComparison (f ≫ g)) ≫
          E.inv.app (SheafOfModules.unit Z.ringCatSheaf) =
        inv (E.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          pullbackUnitComparison (f ≫ g)) :=
    IsIso.eq_inv_of_hom_inv_id hleft
  have hright :
      (E.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        pullbackUnitComparison (f ≫ g)) ≫
          (inv (pullbackUnitComparison f) ≫
            (AlgebraicGeometry.Scheme.Modules.pullback f).map
              (inv (pullbackUnitComparison g))) = 𝟙 _ := by
    have hmap : (AlgebraicGeometry.Scheme.Modules.pullback f).map
        (inv (pullbackUnitComparison g)) =
        inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g)) :=
      Functor.map_inv _ _
    rw [h, hmap]
    calc
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g) ≫ pullbackUnitComparison f) ≫
          (inv (pullbackUnitComparison f) ≫
            inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (pullbackUnitComparison g))) =
        (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g) ≫
          ((pullbackUnitComparison f ≫ inv (pullbackUnitComparison f)) ≫
            inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (pullbackUnitComparison g))) := by
          exact (Category.assoc _ _ _).trans
            (congrArg (fun q =>
              (AlgebraicGeometry.Scheme.Modules.pullback f).map
                (pullbackUnitComparison g) ≫ q)
              (Category.assoc _ _ _).symm)
      _ = (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g) ≫
          (𝟙 _ ≫ inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (pullbackUnitComparison g))) := by
          exact congrArg (fun q =>
            (AlgebraicGeometry.Scheme.Modules.pullback f).map
              (pullbackUnitComparison g) ≫
              (q ≫ inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
                (pullbackUnitComparison g))))
            (IsIso.hom_inv_id _)
      _ = (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g) ≫
          inv ((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (pullbackUnitComparison g)) :=
        congrArg (fun q =>
          (AlgebraicGeometry.Scheme.Modules.pullback f).map
            (pullbackUnitComparison g) ≫ q) (Category.id_comp _)
      _ = 𝟙 _ := IsIso.hom_inv_id _
  have hright_inv :
      inv (pullbackUnitComparison f) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback f).map
            (inv (pullbackUnitComparison g)) =
        inv (E.hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          pullbackUnitComparison (f ≫ g)) :=
    IsIso.eq_inv_of_hom_inv_id hright
  exact hleft_inv.trans hright_inv.symm

universe v w

private theorem homEquiv_comp_conjugate
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {c : C} {d : D} (t : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ t) =
      adj₁.homEquiv c d t ≫
        (conjugateEquiv adj₁ adj₂ α).app d := by
  change adj₂.unit.app c ≫ R₂.map (α.app c ≫ t) =
    (adj₁.unit.app c ≫ R₁.map t) ≫
      (conjugateEquiv adj₁ adj₂ α).app d
  rw [Functor.map_comp]
  erw [← Category.assoc]
  erw [← (unit_conjugateEquiv adj₁ adj₂ α c)]
  rw [Category.assoc]
  erw [← (conjugateEquiv adj₁ adj₂ α).naturality]
  exact (Category.assoc _ _ _).symm

theorem pullbackUnitComparison_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app
        (SheafOfModules.unit Z.ringCatSheaf) ≫
      pullbackUnitComparison (f ≫ g) =
    (AlgebraicGeometry.Scheme.Modules.pullback f).map
      (pullbackUnitComparison g) ≫ pullbackUnitComparison f := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  letI : (SheafOfModules.pushforward (f ≫ g).toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).isRightAdjoint
  have hpc_f :
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (pullbackUnitComparison f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    unfold pullbackUnitComparison
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hpc_g :
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (pullbackUnitComparison g) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    unfold pullbackUnitComparison
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hpc_fg :
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        (pullbackUnitComparison (f ≫ g)) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
    unfold pullbackUnitComparison
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  let A := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f)
  let B := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let E := AlgebraicGeometry.Scheme.Modules.pullbackComp f g
  let P := AlgebraicGeometry.Scheme.Modules.pushforwardComp f g
  have hmate : conjugateEquiv B A E.hom = P.inv := by
    have hcomp : P.hom ≫ conjugateEquiv B A E.hom = 𝟙 _ := by
      rw [← AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv]
      rw [conjugateEquiv_comp]
      rw [E.hom_inv_id]
      exact conjugateEquiv_id A
    have hinv : P.inv = inv P.hom :=
      IsIso.eq_inv_of_hom_inv_id (P.hom_inv_id)
    exact (IsIso.eq_inv_of_hom_inv_id hcomp).trans hinv.symm
  apply (A.homEquiv _ _).injective
  have hfirst :
      A.homEquiv _ _ (E.hom.app _ ≫ pullbackUnitComparison (f ≫ g)) =
        B.homEquiv _ _ (pullbackUnitComparison (f ≫ g)) ≫
          (conjugateEquiv B A E.hom).app _ :=
    homEquiv_comp_conjugate B A E.hom _
  have hsecond :
      B.homEquiv _ _ (pullbackUnitComparison (f ≫ g)) ≫
          (conjugateEquiv B A E.hom).app _ =
        SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom ≫
          P.inv.app (SheafOfModules.unit X.ringCatSheaf) := by
      rw [hmate]
      exact congrArg (fun q => q ≫ P.inv.app _) 
        (hpc_fg)
  have hthird :
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom ≫
          P.inv.app (SheafOfModules.unit X.ringCatSheaf) =
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward g).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
      rw [unitToPushforwardObjUnit_comp]
      change
        (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward g).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          P.hom.app (SheafOfModules.unit X.ringCatSheaf)) ≫
            P.inv.app (SheafOfModules.unit X.ringCatSheaf) =
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
            (AlgebraicGeometry.Scheme.Modules.pushforward g).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      let a := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
      let b := (AlgebraicGeometry.Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      let q := P.hom.app (SheafOfModules.unit X.ringCatSheaf)
      let r := P.inv.app (SheafOfModules.unit X.ringCatSheaf)
      change (a ≫ b ≫ q) ≫ r = a ≫ b
      have h₁ : (a ≫ b ≫ q) ≫ r = a ≫ b ≫ (q ≫ r) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => a ≫ t) (Category.assoc _ _ _))
      have h₂ : a ≫ b ≫ (q ≫ r) = a ≫ b ≫ 𝟙 _ :=
        congrArg (fun t => a ≫ b ≫ t) (P.hom_inv_id_app _)
      have h₃ : a ≫ b ≫ 𝟙 _ = a ≫ b :=
        congrArg (fun t => a ≫ t) (Category.comp_id _)
      exact h₁.trans (h₂.trans h₃)
  have hfourth :
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      A.homEquiv _ _
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (pullbackUnitComparison g) ≫ pullbackUnitComparison f) := by
      change
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward g).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _
          ((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (pullbackUnitComparison g) ≫ pullbackUnitComparison f)
      change
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward g).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
            ((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (pullbackUnitComparison g) ≫ pullbackUnitComparison f))
      rw [(AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
        (pullbackUnitComparison g) (pullbackUnitComparison f)]
      rw [hpc_f]
      have houter :=
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right
          (pullbackUnitComparison g)
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      exact (houter.trans
        (congrArg (fun q => q ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward g).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) hpc_g)).symm
  exact hfirst.trans (hsecond.trans (hthird.trans hfourth))

/-- Pulling a section back twice agrees with pulling it back along the
composite scheme morphism. -/
theorem pullbackSection_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g))
    (hfg : IsIso (pullbackUnitComparison (f ≫ g)))
    (s : M.sections) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M)
      (pullbackSection (f ≫ g) M hfg s) =
    pullbackSection f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
      (pullbackSection g M hg s) :=
  pullbackSection_comp_of_unitComparison f g M hf hg hfg s
    (pullbackUnitComparison_inverse_comp_of_comp f g hf hg hfg
      (pullbackUnitComparison_comp f g))

/-- Iterated pullback, followed by the canonical composition isomorphism and
transport along an equality of composite maps, is the direct pullback along
the equal map.  This packages the two coherence steps used by parameter-chart
overlap constructions. -/
theorem sectionsMap_pullbackComp_pullbackCongr_pullbackSection
    {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) (M : Z.Modules)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g))
    (hfg : IsIso (pullbackUnitComparison (f ≫ g)))
    (hq : IsIso (pullbackUnitComparison q)) (s : M.sections) :
    SheafOfModules.sectionsMap
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M).hom)
      (pullbackSection f
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
        (pullbackSection g M hg s)) =
      pullbackSection q M hq s := by
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M
  let C := (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M
  let t := pullbackSection (f ≫ g) M hfg s
  let r := pullbackSection f
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
    (pullbackSection g M hg s)
  have hcomp : SheafOfModules.sectionsMap B.hom r = t := by
    have hraw := pullbackSection_comp f g M hf hg hfg s
    refine (congrArg (SheafOfModules.sectionsMap B.hom) hraw.symm).trans ?_
    calc
      SheafOfModules.sectionsMap B.hom
          (SheafOfModules.sectionsMap B.inv t) =
        SheafOfModules.sectionsMap (B.inv ≫ B.hom) t :=
          (SheafOfModules.sectionsMap_comp B.inv B.hom t).symm
      _ = SheafOfModules.sectionsMap (𝟙 _) t :=
        congrArg (fun z => SheafOfModules.sectionsMap z t) B.inv_hom_id
      _ = t := SheafOfModules.sectionsMap_id t
  have hcongr : SheafOfModules.sectionsMap C.hom t =
      pullbackSection q M hq s :=
    sectionsMap_pullbackCongr_pullbackSection (f ≫ g) q h M hfg hq s
  exact (SheafOfModules.sectionsMap_comp B.hom C.hom r).trans
    ((congrArg (SheafOfModules.sectionsMap C.hom) hcomp).trans hcongr)

/-- Pulling a section around either side of a commutative square gives the
same section after transport by the canonical pseudofunctorial isomorphism. -/
theorem sectionsMap_pullbackSquare_pullbackSection
    {Y Y' Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (M : Z.Modules)
    (hf : IsIso (pullbackUnitComparison f))
    (hg : IsIso (pullbackUnitComparison g))
    (hfg : IsIso (pullbackUnitComparison (f ≫ g)))
    (hf' : IsIso (pullbackUnitComparison f'))
    (hg' : IsIso (pullbackUnitComparison g'))
    (hf'g' : IsIso (pullbackUnitComparison (f' ≫ g')))
    (s : M.sections) :
    SheafOfModules.sectionsMap
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M ≪≫
          (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M) ≪≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp f' g').app M).symm).hom)
      (pullbackSection f
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
        (pullbackSection g M hg s)) =
      pullbackSection f'
        ((AlgebraicGeometry.Scheme.Modules.pullback g').obj M) hf'
        (pullbackSection g' M hg' s) := by
  let A := (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M
  let C := (AlgebraicGeometry.Scheme.Modules.pullbackComp f' g').app M
  let r := pullbackSection f
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) hf
    (pullbackSection g M hg s)
  let t := pullbackSection (f' ≫ g') M hf'g' s
  have hleft : SheafOfModules.sectionsMap (A ≪≫ B).hom r = t :=
    sectionsMap_pullbackComp_pullbackCongr_pullbackSection
      f g (f' ≫ g') h M hf hg hfg hf'g' s
  calc
    SheafOfModules.sectionsMap ((A ≪≫ B) ≪≫ C.symm).hom r =
        SheafOfModules.sectionsMap C.inv
          (SheafOfModules.sectionsMap (A ≪≫ B).hom r) :=
      SheafOfModules.sectionsMap_comp (A ≪≫ B).hom C.inv r
    _ = SheafOfModules.sectionsMap C.inv t :=
      congrArg (SheafOfModules.sectionsMap C.inv) hleft
    _ = pullbackSection f'
        ((AlgebraicGeometry.Scheme.Modules.pullback g').obj M) hf'
        (pullbackSection g' M hg' s) :=
      pullbackSection_comp f' g' M hf' hg' hf'g' s


/-- Addition of arbitrary module sections, expressed through their maps out
of the unit module. -/
noncomputable def addSections {E : X.Modules}
    (s t : E.sections) : E.sections := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  exact E'.unitHomEquiv (E'.unitHomEquiv.symm s + E'.unitHomEquiv.symm t)

/-- Pullback commutes with addition of arbitrary module sections. -/
theorem pullbackSection_addSections {Y : Scheme.{u}} (f : X ⟶ Y)
    {E : Y.Modules} (hunit : IsIso (pullbackUnitComparison f))
    (s t : E.sections) :
    pullbackSection f E hunit (addSections s t) =
      addSections (pullbackSection f E hunit s)
        (pullbackSection f E hunit t) := by
  let q₀ : SheafOfModules.unit X.ringCatSheaf ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (SheafOfModules.unit Y.ringCatSheaf) := Classical.choose hunit.out
  simp only [addSections]
  let E' : SheafOfModules.{u} Y.ringCatSheaf := E
  let F := AlgebraicGeometry.Scheme.Modules.pullback f
  letI : F.Additive := by
    dsimp [F]
    infer_instance
  let E'' : SheafOfModules.{u} X.ringCatSheaf := F.obj E'
  change pullbackSection f E' hunit (E'.unitHomEquiv
    (E'.unitHomEquiv.symm s + E'.unitHomEquiv.symm t)) =
    E''.unitHomEquiv
      (E''.unitHomEquiv.symm (pullbackSection f E' hunit s) +
        E''.unitHomEquiv.symm (pullbackSection f E' hunit t))
  let A : SheafOfModules.{u} X.ringCatSheaf :=
    F.obj (SheafOfModules.unit Y.ringCatSheaf)
  let q : SheafOfModules.unit X.ringCatSheaf ⟶ A := q₀
  let m : SheafOfModules.unit Y.ringCatSheaf ⟶ E' := E'.unitHomEquiv.symm s
  let n : SheafOfModules.unit Y.ringCatSheaf ⟶ E' := E'.unitHomEquiv.symm t
  let a : A ⟶ E'' := F.map m
  let d : A ⟶ E'' := F.map n
  apply E''.unitHomEquiv.symm.injective
  rw [pullbackSection_unitHomEquiv_symm]
  simp only [Equiv.symm_apply_apply]
  rw [pullbackSection_unitHomEquiv_symm]
  rw [pullbackSection_unitHomEquiv_symm]
  dsimp only [E']
  simp only [Equiv.symm_apply_apply]
  change q ≫ (F.map (m + n) : A ⟶ E'') = (q ≫ a) + (q ≫ d)
  have hmap : (F.map (m + n) : A ⟶ E'') = a + d := F.map_add
  rw [hmap]
  exact Preadditive.comp_add _ _ _ q a d

/-- Mapping sections along a module morphism commutes with their addition. -/
theorem sectionsMap_addSections {E F : X.Modules} (g : E ⟶ F)
    (s t : E.sections) :
    SheafOfModules.sectionsMap g (addSections s t) =
      addSections (SheafOfModules.sectionsMap g s)
        (SheafOfModules.sectionsMap g t) := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  let F' : SheafOfModules.{u} X.ringCatSheaf := F
  change E' ⟶ F' at g
  apply F'.unitHomEquiv.symm.injective
  calc
    F'.unitHomEquiv.symm (SheafOfModules.sectionsMap g (addSections s t)) =
        E'.unitHomEquiv.symm (addSections s t) ≫ g :=
      (E'.unitHomEquiv_symm_comp _ g).symm
    _ = (E'.unitHomEquiv.symm s + E'.unitHomEquiv.symm t) ≫ g := by
      simp only [addSections, Equiv.symm_apply_apply]
    _ = ((E'.unitHomEquiv.symm s ≫ g) + (E'.unitHomEquiv.symm t ≫ g) :
        SheafOfModules.unit X.ringCatSheaf ⟶ F') := by
      rw [Preadditive.add_comp]
    _ = (F'.unitHomEquiv.symm (SheafOfModules.sectionsMap g s) +
        F'.unitHomEquiv.symm (SheafOfModules.sectionsMap g t) :
          SheafOfModules.unit X.ringCatSheaf ⟶ F') := by
      rw [E'.unitHomEquiv_symm_comp, E'.unitHomEquiv_symm_comp]
    _ = F'.unitHomEquiv.symm
        (addSections (SheafOfModules.sectionsMap g s)
          (SheafOfModules.sectionsMap g t)) := by
      simp only [addSections, Equiv.symm_apply_apply]

noncomputable def freeCoordinateMap (I : Type u) (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf := by
  classical
  exact (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.symm
    (fun j ↦ if j = i then
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)
    else (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv 0)

noncomputable def unitSectionAtTop
    (s : (SheafOfModules.unit X.ringCatSheaf).sections) : Γ(X, ⊤) :=
  s.val (Opposite.op ⊤)

/-- The global scalar represented by an endomorphism of the structure-sheaf
module.  This is the coefficient that appears in a transition matrix between
free trivializations. -/
noncomputable def unitEndomorphismValue
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Γ(X, ⊤) :=
  unitSectionAtTop ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv a)

/-- A global regular function, regarded as a compatible section of the
structure-sheaf module on every open subset. -/
noncomputable def unitSectionOfRegularFunction (r : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (M := (SheafOfModules.unit X.ringCatSheaf).val)
    (fun U => X.presheaf.map
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
    (by
      intro U V h
      change X.presheaf.map h
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) =
        X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op r
      have hfun : X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫
          X.presheaf.map h =
          X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op := by
        rw [← X.presheaf.map_comp]
        rfl
      exact congrArg (fun q => q.hom r) hfun)

/-- Multiplication by a global regular function as an endomorphism of the
unit module. -/
noncomputable def unitEndomorphismOfRegularFunction (r : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
    (unitSectionOfRegularFunction r)

/-- Recovering the global coefficient of the endomorphism associated with a
regular function gives the original function. -/
theorem unitEndomorphismValue_ofRegularFunction (r : Γ(X, ⊤)) :
    unitEndomorphismValue (X := X) (unitEndomorphismOfRegularFunction r) = r := by
  unfold unitEndomorphismValue unitSectionAtTop unitEndomorphismOfRegularFunction
  rw [Equiv.apply_symm_apply]
  unfold unitSectionOfRegularFunction
  change X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op r = r
  simp

/-- An endomorphism of the structure-sheaf module is determined by its global
scalar coefficient. -/
theorem unitEndomorphismOfRegularFunction_value
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    unitEndomorphismOfRegularFunction (X := X)
      (unitEndomorphismValue (X := X) a) = a := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  ext U
  simp only [unitEndomorphismOfRegularFunction, Equiv.apply_symm_apply]
  unfold unitSectionOfRegularFunction unitEndomorphismValue unitSectionAtTop
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(X, ⊤))) =
      (a.val.app U).hom (1 : Γ(X, U.unop))
  have hnat := a.val.naturality
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hnat1 := congrArg (fun q => q.hom (1 : Γ(X, ⊤))) hnat
  let r : Γ(X, ⊤) →+* Γ(X, U.unop) :=
    (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
  have hnat' : (a.val.app U).hom (r 1) =
      r ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(X, ⊤))) := by
    exact hnat1
  have hr1 : r 1 = 1 := by simp [r]
  rw [← hr1]
  exact hnat'.symm

/-- The constant function one acts as the identity on the unit module. -/
theorem unitEndomorphismOfRegularFunction_one :
    unitEndomorphismOfRegularFunction (X := X) (1 : Γ(X, ⊤)) = 𝟙 _ := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  ext U
  simp only [unitEndomorphismOfRegularFunction, Equiv.apply_symm_apply]
  unfold unitSectionOfRegularFunction
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (1 : Γ(X, ⊤)) = 1
  exact map_one _

/-- The constant function zero acts as the zero endomorphism of the unit
module. -/
theorem unitEndomorphismOfRegularFunction_zero :
    unitEndomorphismOfRegularFunction (X := X) (0 : Γ(X, ⊤)) = 0 := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  ext U
  simp only [unitEndomorphismOfRegularFunction, Equiv.apply_symm_apply]
  unfold unitSectionOfRegularFunction
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (0 : Γ(X, ⊤)) = 0
  exact map_zero _

/-- Multiplication of global regular functions becomes composition of their
unit-module endomorphisms. -/
theorem unitEndomorphismOfRegularFunction_mul (r s : Γ(X, ⊤)) :
    unitEndomorphismOfRegularFunction (X := X) (r * s) =
      unitEndomorphismOfRegularFunction r ≫ unitEndomorphismOfRegularFunction s := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  ext U
  simp only [unitEndomorphismOfRegularFunction, Equiv.apply_symm_apply,
    SheafOfModules.unitHomEquiv_comp_apply]
  unfold unitSectionOfRegularFunction
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r * s) =
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r *
      X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  exact map_mul _ _ _

/-- A unit-valued regular function acts invertibly on the unit module. -/
theorem isIso_unitEndomorphismOfRegularFunction_of_isUnit
    (r : Γ(X, ⊤)) (hr : IsUnit r) :
    IsIso (unitEndomorphismOfRegularFunction (X := X) r) := by
  rcases hr with ⟨u, rfl⟩
  refine IsIso.mk ⟨unitEndomorphismOfRegularFunction (X := X) (↑u⁻¹), ?_, ?_⟩
  · rw [← unitEndomorphismOfRegularFunction_mul]
    simpa using unitEndomorphismOfRegularFunction_one (X := X)
  · rw [← unitEndomorphismOfRegularFunction_mul]
    simpa using unitEndomorphismOfRegularFunction_one (X := X)

/-- Composition of structure-sheaf endomorphisms becomes multiplication of
their global scalar coefficients. -/
theorem unitEndomorphismValue_comp
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    unitEndomorphismValue (X := X) (a ≫ b) =
      unitEndomorphismValue (X := X) a * unitEndomorphismValue (X := X) b := by
  let R := X.ringCatSheaf.obj.obj (Opposite.op ⊤)
  let a' : R →ₗ[R] R := (a.val.app (Opposite.op ⊤)).hom
  let b' : R →ₗ[R] R := (b.val.app (Opposite.op ⊤)).hom
  let a₁ : R := a' (1 : R)
  let b₁ : R := b' (1 : R)
  change b' (a' (1 : R)) = a₁ * b₁
  change b' a₁ = a₁ * b₁
  calc
    b' a₁ = b' (a₁ • (1 : R)) := by rw [smul_eq_mul, mul_one]
    _ = a₁ • b₁ := by
      simpa [b₁] using b'.map_smul a₁ (1 : R)
    _ = a₁ * b₁ := by rw [smul_eq_mul]

/-- Addition of structure-sheaf endomorphisms becomes addition of their
global scalar coefficients. -/
theorem unitEndomorphismValue_add
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    unitEndomorphismValue (X := X) (a + b) =
      unitEndomorphismValue (X := X) a + unitEndomorphismValue (X := X) b := by
  simp only [unitEndomorphismValue, unitSectionAtTop,
    SheafOfModules.unitHomEquiv_apply_coe]
  rfl

/-- Addition of global regular functions becomes addition of their
endomorphisms of the structure-sheaf module. -/
theorem unitEndomorphismOfRegularFunction_add (r s : Γ(X, ⊤)) :
    unitEndomorphismOfRegularFunction (X := X) (r + s) =
      unitEndomorphismOfRegularFunction r + unitEndomorphismOfRegularFunction s := by
  rw [← unitEndomorphismOfRegularFunction_value
    (X := X) (unitEndomorphismOfRegularFunction r +
      unitEndomorphismOfRegularFunction s)]
  congr 1
  rw [unitEndomorphismValue_add,
    unitEndomorphismValue_ofRegularFunction,
    unitEndomorphismValue_ofRegularFunction]

/-- An endomorphism of the structure sheaf acts on a global scalar section
by multiplication with its coefficient. -/
theorem unitSectionAtTop_sectionsMap
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : (SheafOfModules.unit X.ringCatSheaf).sections) :
    unitSectionAtTop (X := X) (SheafOfModules.sectionsMap a s) =
      unitEndomorphismValue (X := X) a * unitSectionAtTop (X := X) s := by
  let R := X.presheaf.obj (Opposite.op ⊤)
  let a' : R →ₗ[R] R := (a.val.app (Opposite.op ⊤)).hom
  let s' : R := s.val (Opposite.op ⊤)
  let a₁ : R := a' (1 : R)
  change a' s' = a₁ * s'
  calc
    a' s' = a' (s' • (1 : R)) := by rw [smul_eq_mul, mul_one]
    _ = s' • a₁ := by
      simpa [a₁] using a'.map_smul s' (1 : R)
    _ = a₁ * s' := by simpa [smul_eq_mul] using mul_comm s' a₁

noncomputable def freeSectionCoordinate (I : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (i : I) :
    Γ(X, ⊤) :=
  unitSectionAtTop
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
      ((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s ≫
        freeCoordinateMap I i))

/-- Multiply a section of a free module by a scalar endomorphism of the
structure sheaf. -/
noncomputable def scaleFreeSection (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).sections :=
  (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv
    (a ≫ (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s)

/-- Each coordinate of a scalar multiple is multiplied by the corresponding
global scalar coefficient. -/
theorem freeSectionCoordinate_scale
    (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (i : I) :
    freeSectionCoordinate (X := X) I (scaleFreeSection (X := X) I a s) i =
      unitEndomorphismValue (X := X) a * freeSectionCoordinate (X := X) I s i := by
  unfold freeSectionCoordinate scaleFreeSection
  rw [Equiv.symm_apply_apply]
  rw [Category.assoc]
  let c : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s ≫
      freeCoordinateMap I i
  change unitSectionAtTop
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (a ≫ c)) = _
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  rw [unitSectionAtTop_sectionsMap]
  change unitEndomorphismValue (X := X) c * unitEndomorphismValue (X := X) a = _
  rw [mul_comm]
  rfl

/-- Addition of free-module sections, expressed through their representing
maps from the unit module. -/
noncomputable def addFreeSections (I : Type u)
    (s t : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).sections :=
  (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv
    ((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s +
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm t)

/-- Coordinates of a sum are sums of coordinates. -/
theorem freeSectionCoordinate_add
    (I : Type u)
    (s t : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (i : I) :
    freeSectionCoordinate (X := X) I (addFreeSections (X := X) I s t) i =
      freeSectionCoordinate (X := X) I s i + freeSectionCoordinate (X := X) I t i := by
  unfold freeSectionCoordinate addFreeSections
  rw [Equiv.symm_apply_apply, Preadditive.add_comp]
  change unitEndomorphismValue (X := X)
    ((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s ≫
      freeCoordinateMap I i +
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm t ≫
        freeCoordinateMap I i) = _
  rw [unitEndomorphismValue_add]
  rfl

noncomputable def freeSectionZeroIdeal (I : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    AlgebraicGeometry.Scheme.IdealSheafData X :=
  AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
    (Ideal.span (Set.range (freeSectionCoordinate (X := X) I s)))

/-- A rank-two free section has a zero ideal generated by its two scalar
coordinates.  This makes the regular-sequence calculation for a rank-two
zero locus a literal two-element quotient calculation. -/
theorem ideal_span_range_ulift_fin_two {R : Type*} [Semiring R]
    (g : ULift (Fin 2) → R) :
    Ideal.span (Set.range g) =
      Ideal.span {g (ULift.up 0)} ⊔ Ideal.span {g (ULift.up 1)} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro x ⟨i, rfl⟩
    rcases i with ⟨i⟩
    fin_cases i
    · exact (show Ideal.span {g (ULift.up 0)} ≤
        Ideal.span {g (ULift.up 0)} ⊔ Ideal.span {g (ULift.up 1)} from le_sup_left)
        (Ideal.subset_span (s := {g (ULift.up 0)}) (Set.mem_singleton _))
    · exact (show Ideal.span {g (ULift.up 1)} ≤
        Ideal.span {g (ULift.up 0)} ⊔ Ideal.span {g (ULift.up 1)} from le_sup_right)
        (Ideal.subset_span (s := {g (ULift.up 1)}) (Set.mem_singleton _))
  · apply sup_le
    · apply Ideal.span_le.2
      rintro x rfl
      exact Ideal.subset_span ⟨ULift.up 0, rfl⟩
    · apply Ideal.span_le.2
      rintro x rfl
      exact Ideal.subset_span ⟨ULift.up 1, rfl⟩

/-- The zero ideal of a rank-two free section is the two-element ideal of its
two coordinates. -/
theorem freeSectionZeroIdeal_ulift_fin_two_eq
    (s : (SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin 2))).sections) :
    freeSectionZeroIdeal (X := X) (ULift (Fin 2)) s =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {freeSectionCoordinate (X := X) (ULift (Fin 2)) s (ULift.up 0)} ⊔
          Ideal.span {freeSectionCoordinate (X := X) (ULift (Fin 2)) s (ULift.up 1)}) := by
  unfold freeSectionZeroIdeal
  rw [ideal_span_range_ulift_fin_two]

noncomputable def freeSectionZeroSubscheme (I : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) : Scheme.{u} :=
  (freeSectionZeroIdeal (X := X) I s).subscheme

noncomputable def freeSectionZeroSubschemeι (I : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    freeSectionZeroSubscheme (X := X) I s ⟶ X :=
  (freeSectionZeroIdeal (X := X) I s).subschemeι

theorem freeSectionCoordinate_mem_zeroIdeal [AlgebraicGeometry.IsAffine X]
    (I : Type u) (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (i : I) :
    freeSectionCoordinate (X := X) I s i ∈
      (freeSectionZeroIdeal (X := X) I s).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩ := by
  rw [freeSectionZeroIdeal,
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal]
  simpa using (Ideal.subset_span (s := Set.range
    (freeSectionCoordinate (X := X) I s)) ⟨i, rfl⟩)

end BundleSectionZeroLocus
end PfaffianDescent

namespace PfaffianDescent.BundleSectionZeroLocus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

/-- The zero locus defined from scalar coordinates is a closed subscheme. -/
theorem isClosedImmersion_freeSectionZeroSubschemeι
    (I : Type u) (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    IsClosedImmersion
      (freeSectionZeroSubschemeι (X := X) I s) := by
  change IsClosedImmersion (freeSectionZeroIdeal (X := X) I s).subschemeι
  infer_instance

end PfaffianDescent.BundleSectionZeroLocus

namespace PfaffianDescent.BundleSectionZeroLocus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

/-- The scalar coordinate of a section after choosing a trivialization of its
module sheaf by a free module. -/
noncomputable def sectionCoordinateOfFreeIso
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) (i : I) : Γ(X, ⊤) :=
  freeSectionCoordinate (X := X) I (SheafOfModules.sectionsMap e.inv s) i

/-- The closed ideal defined by the scalar coordinates of a section in a
chosen free trivialization. -/
noncomputable def sectionZeroIdealOfFreeIso
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) : AlgebraicGeometry.Scheme.IdealSheafData X :=
  freeSectionZeroIdeal (X := X) I (SheafOfModules.sectionsMap e.inv s)

/-- In a rank-two trivialization, the section zero ideal is generated by the
two displayed scalar coordinates. -/
theorem sectionZeroIdealOfFreeIso_ulift_fin_two_eq
    {E : X.Modules}
    (e : SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin 2)) ≅ E)
    (s : E.sections) :
    sectionZeroIdealOfFreeIso (X := X) (ULift (Fin 2)) e s =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {sectionCoordinateOfFreeIso (X := X) (ULift (Fin 2)) e s (ULift.up 0)} ⊔
          Ideal.span {sectionCoordinateOfFreeIso (X := X) (ULift (Fin 2)) e s (ULift.up 1)}) := by
  unfold sectionZeroIdealOfFreeIso sectionCoordinateOfFreeIso
  exact freeSectionZeroIdeal_ulift_fin_two_eq _

/-- The scheme-theoretic zero locus of a section in a chosen free
trivialization. -/
noncomputable def sectionZeroSubschemeOfFreeIso
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) : Scheme.{u} :=
  (sectionZeroIdealOfFreeIso (X := X) I e s).subscheme

noncomputable def sectionZeroSubschemeOfFreeIsoι
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) : sectionZeroSubschemeOfFreeIso (X := X) I e s ⟶ X :=
  (sectionZeroIdealOfFreeIso (X := X) I e s).subschemeι

theorem sectionCoordinateOfFreeIso_mem_zeroIdeal [AlgebraicGeometry.IsAffine X]
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) (i : I) :
    sectionCoordinateOfFreeIso (X := X) I e s i ∈
      (sectionZeroIdealOfFreeIso (X := X) I e s).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩ := by
  exact freeSectionCoordinate_mem_zeroIdeal I
    (SheafOfModules.sectionsMap e.inv s) i

theorem isClosedImmersion_sectionZeroSubschemeOfFreeIsoι
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s : E.sections) :
    IsClosedImmersion (sectionZeroSubschemeOfFreeIsoι (X := X) I e s) := by
  change IsClosedImmersion (sectionZeroIdealOfFreeIso (X := X) I e s).subschemeι
  infer_instance

/-- Equality of the generated coordinate ideals identifies the corresponding
closed zero subschemes.  This is the exact algebraic compatibility condition
to verify on overlaps of free trivializations. -/
theorem freeSectionZeroIdeal_eq_of_coordinateSpan_eq
    (I J : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) J).sections)
    (h : Ideal.span (Set.range (freeSectionCoordinate (X := X) I s)) =
      Ideal.span (Set.range (freeSectionCoordinate (X := X) J t))) :
    freeSectionZeroIdeal (X := X) I s =
      freeSectionZeroIdeal (X := X) J t := by
  unfold freeSectionZeroIdeal
  rw [h]

/-- The preceding coordinate-span equality also identifies the resulting
zero-locus schemes. -/
theorem freeSectionZeroSubscheme_eq_of_coordinateSpan_eq
    (I J : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) J).sections)
    (h : Ideal.span (Set.range (freeSectionCoordinate (X := X) I s)) =
      Ideal.span (Set.range (freeSectionCoordinate (X := X) J t))) :
    freeSectionZeroSubscheme (X := X) I s =
      freeSectionZeroSubscheme (X := X) J t := by
  rw [freeSectionZeroSubscheme, freeSectionZeroSubscheme,
    freeSectionZeroIdeal_eq_of_coordinateSpan_eq I J s t h]

/-- On an affine chart, coordinate-wise containment gives containment of
the associated zero-locus ideals.  Applying this in both directions is the
local algebra needed to make zero loci independent of a free basis. -/
theorem freeSectionZeroIdeal_le_of_coordinates_mem
    [AlgebraicGeometry.IsAffine X] (I J : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) J).sections)
    (h : ∀ j : J, freeSectionCoordinate (X := X) J t j ∈
      Ideal.span (Set.range (freeSectionCoordinate (X := X) I s))) :
    freeSectionZeroIdeal (X := X) J t ≤
      freeSectionZeroIdeal (X := X) I s := by
  apply AlgebraicGeometry.Scheme.IdealSheafData.le_of_isAffine
  rw [freeSectionZeroIdeal, freeSectionZeroIdeal,
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal,
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal]
  apply Ideal.map_mono
  apply Ideal.span_le.2
  rintro x ⟨j, rfl⟩
  exact h j

/-- Mutual coordinate-wise containment identifies the two zero-locus ideals
on an affine chart. -/
theorem freeSectionZeroIdeal_eq_of_coordinates_mem
    [AlgebraicGeometry.IsAffine X] (I J : Type u)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) J).sections)
    (hst : ∀ j : J, freeSectionCoordinate (X := X) J t j ∈
      Ideal.span (Set.range (freeSectionCoordinate (X := X) I s)))
    (hts : ∀ i : I, freeSectionCoordinate (X := X) I s i ∈
      Ideal.span (Set.range (freeSectionCoordinate (X := X) J t))) :
    freeSectionZeroIdeal (X := X) I s =
      freeSectionZeroIdeal (X := X) J t := by
  apply le_antisymm
  · exact freeSectionZeroIdeal_le_of_coordinates_mem J I t s hts
  · exact freeSectionZeroIdeal_le_of_coordinates_mem I J s t hst

/-- Scaling every coordinate of a free-module section by an invertible global
function does not change its scheme-theoretic zero ideal.  This is the
affine-chart identity used to identify the two homogeneous-coordinate charts
of a pencil. -/
theorem freeSectionZeroIdeal_scaleFreeSection_eq
    [AlgebraicGeometry.IsAffine X] (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (ha : IsUnit (unitEndomorphismValue (X := X) a)) :
    freeSectionZeroIdeal (X := X) I (scaleFreeSection (X := X) I a s) =
      freeSectionZeroIdeal (X := X) I s := by
  obtain ⟨u, hu⟩ := ha
  apply freeSectionZeroIdeal_eq_of_coordinates_mem I I
  · intro i
    have hcoordinate : freeSectionCoordinate (X := X) I s i =
        (↑(u⁻¹) : Γ(X, ⊤)) * freeSectionCoordinate (X := X) I
          (scaleFreeSection (X := X) I a s) i := by
      rw [freeSectionCoordinate_scale, ← hu]
      calc
        freeSectionCoordinate (X := X) I s i =
            (↑(u⁻¹) : Γ(X, ⊤)) * ↑u *
              freeSectionCoordinate (X := X) I s i := by
          rw [Units.inv_mul, one_mul]
        _ = (↑(u⁻¹) : Γ(X, ⊤)) *
            (↑u * freeSectionCoordinate (X := X) I s i) := by
          rw [mul_assoc]
    rw [hcoordinate]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨i, rfl⟩)
  · intro i
    rw [freeSectionCoordinate_scale, ← hu]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨i, rfl⟩)

/-- The zero subscheme itself is unchanged by multiplication of all free
coordinates by an invertible global function. -/
theorem freeSectionZeroSubscheme_scaleFreeSection_eq
    [AlgebraicGeometry.IsAffine X] (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (ha : IsUnit (unitEndomorphismValue (X := X) a)) :
    freeSectionZeroSubscheme (X := X) I (scaleFreeSection (X := X) I a s) =
      freeSectionZeroSubscheme (X := X) I s := by
  rw [freeSectionZeroSubscheme, freeSectionZeroSubscheme,
    freeSectionZeroIdeal_scaleFreeSection_eq I a s ha]

/-- An invertible endomorphism of the structure-sheaf module has an
invertible global scalar coefficient. -/
theorem isUnit_unitEndomorphismValue_of_isIso
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a] :
    IsUnit (unitEndomorphismValue (X := X) a) := by
  apply IsUnit.of_mul_eq_one (unitEndomorphismValue (X := X) (inv a))
  rw [← unitEndomorphismValue_comp, IsIso.hom_inv_id]
  rfl

/-- Scaling free coordinates by an invertible scalar preserves their
globally generated ideal sheaf.  This version uses the equality of the
generating ideals directly, and therefore does not require the source scheme
itself to be affine. -/
theorem freeSectionZeroIdeal_scaleFreeSection_eq_of_isIso_global
    (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a]
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    freeSectionZeroIdeal (X := X) I (scaleFreeSection (X := X) I a s) =
      freeSectionZeroIdeal (X := X) I s := by
  unfold freeSectionZeroIdeal
  congr 1
  obtain ⟨u, hu⟩ := isUnit_unitEndomorphismValue_of_isIso (X := X) a
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro x ⟨i, rfl⟩
    rw [freeSectionCoordinate_scale, ← hu]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (s := Set.range
        (freeSectionCoordinate (X := X) I s)) ⟨i, rfl⟩)
  · apply Ideal.span_le.2
    rintro x ⟨i, rfl⟩
    have hcoordinate : freeSectionCoordinate (X := X) I s i =
        (↑(u⁻¹) : Γ(X, ⊤)) * freeSectionCoordinate (X := X) I
          (scaleFreeSection (X := X) I a s) i := by
      rw [freeSectionCoordinate_scale, ← hu]
      calc
        freeSectionCoordinate (X := X) I s i =
            (↑(u⁻¹) : Γ(X, ⊤)) * ↑u *
              freeSectionCoordinate (X := X) I s i := by
          rw [Units.inv_mul, one_mul]
        _ = (↑(u⁻¹) : Γ(X, ⊤)) *
            (↑u * freeSectionCoordinate (X := X) I s i) := by
          rw [mul_assoc]
    rw [hcoordinate]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (s := Set.range
        (freeSectionCoordinate (X := X) I
          (scaleFreeSection (X := X) I a s))) ⟨i, rfl⟩)

/-- The free-coordinate zero ideal is unchanged by an invertible scalar
endomorphism of the structure sheaf. -/
theorem freeSectionZeroIdeal_scaleFreeSection_eq_of_isIso
    [AlgebraicGeometry.IsAffine X] (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a]
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    freeSectionZeroIdeal (X := X) I (scaleFreeSection (X := X) I a s) =
      freeSectionZeroIdeal (X := X) I s :=
  freeSectionZeroIdeal_scaleFreeSection_eq I a s
    (isUnit_unitEndomorphismValue_of_isIso a)

/-- The free-coordinate zero subscheme is unchanged by an invertible scalar
endomorphism of the structure sheaf. -/
theorem freeSectionZeroSubscheme_scaleFreeSection_eq_of_isIso
    [AlgebraicGeometry.IsAffine X] (I : Type u)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a]
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    freeSectionZeroSubscheme (X := X) I (scaleFreeSection (X := X) I a s) =
      freeSectionZeroSubscheme (X := X) I s :=
  freeSectionZeroSubscheme_scaleFreeSection_eq I a s
    (isUnit_unitEndomorphismValue_of_isIso a)

/-- Multiply an arbitrary module section by a scalar endomorphism of the
structure-sheaf module. -/
noncomputable def scaleSection {E : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : E.sections) : E.sections :=
  E.unitHomEquiv (a ≫ E.unitHomEquiv.symm s)

/-- Mapping a section along a module morphism commutes with multiplication by
a scalar endomorphism of the unit module. -/
theorem sectionsMap_scaleSection {E F : X.Modules} (g : E ⟶ F)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : E.sections) :
    SheafOfModules.sectionsMap g (scaleSection a s) =
      scaleSection a (SheafOfModules.sectionsMap g s) := by
  apply F.unitHomEquiv.symm.injective
  calc
    F.unitHomEquiv.symm (SheafOfModules.sectionsMap g (scaleSection a s)) =
        E.unitHomEquiv.symm (scaleSection a s) ≫ g :=
      (E.unitHomEquiv_symm_comp _ g).symm
    _ = (a ≫ E.unitHomEquiv.symm s) ≫ g := by
      simp only [scaleSection, Equiv.symm_apply_apply]
    _ = a ≫ (E.unitHomEquiv.symm s ≫ g) := Category.assoc _ _ _
    _ = a ≫ F.unitHomEquiv.symm (SheafOfModules.sectionsMap g s) := by
      congr 1
      exact E.unitHomEquiv_symm_comp s g
    _ = F.unitHomEquiv.symm
        (scaleSection a (SheafOfModules.sectionsMap g s)) := by
      simp only [scaleSection, Equiv.symm_apply_apply]

/-- Scalar multiplication distributes over the addition of module sections. -/
theorem scaleSection_addSections {E : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s t : E.sections) :
    scaleSection a (addSections s t) =
      addSections (scaleSection a s) (scaleSection a t) := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  apply E'.unitHomEquiv.symm.injective
  calc
    E'.unitHomEquiv.symm (scaleSection a (addSections s t)) =
        a ≫ E'.unitHomEquiv.symm (addSections s t) := by
      simp only [scaleSection, Equiv.symm_apply_apply]
    _ = a ≫ (E'.unitHomEquiv.symm s + E'.unitHomEquiv.symm t) := by
      simp only [addSections, Equiv.symm_apply_apply]
    _ = (a ≫ E'.unitHomEquiv.symm s) + (a ≫ E'.unitHomEquiv.symm t) := by
      rw [Preadditive.comp_add]
    _ = E'.unitHomEquiv.symm (scaleSection a s) +
        E'.unitHomEquiv.symm (scaleSection a t) := by
      simp only [scaleSection, Equiv.symm_apply_apply]
    _ = E'.unitHomEquiv.symm
        (addSections (scaleSection a s) (scaleSection a t)) := by
      simp only [addSections, Equiv.symm_apply_apply]

/-- Successive scalar multiplications combine by composition of their unit
endomorphisms. -/
theorem scaleSection_scaleSection {E : X.Modules}
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : E.sections) :
    scaleSection a (scaleSection b s) = scaleSection (a ≫ b) s := by
  let E' : SheafOfModules.{u} X.ringCatSheaf := E
  apply E'.unitHomEquiv.symm.injective
  dsimp [E']
  simp only [scaleSection, Equiv.symm_apply_apply]
  exact Category.assoc a b (E.unitHomEquiv.symm s)

/-- Passing to free coordinates commutes with scalar multiplication of a
section. -/
theorem sectionsMap_freeIso_inv_scaleSection
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : E.sections) :
    SheafOfModules.sectionsMap e.inv (scaleSection (X := X) a s) =
      scaleFreeSection (X := X) I a (SheafOfModules.sectionsMap e.inv s) := by
  apply (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm.injective
  calc
    (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inv (scaleSection (X := X) a s)) =
      E.unitHomEquiv.symm (scaleSection (X := X) a s) ≫ e.inv :=
        (E.unitHomEquiv_symm_comp _ e.inv).symm
    _ = (a ≫ E.unitHomEquiv.symm s) ≫ e.inv := by
      simp only [scaleSection, Equiv.symm_apply_apply]
    _ = a ≫ (E.unitHomEquiv.symm s ≫ e.inv) :=
      Category.assoc a (E.unitHomEquiv.symm s) e.inv
    _ = a ≫ (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inv s) := by
      rw [E.unitHomEquiv_symm_comp s e.inv]
    _ = (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (scaleFreeSection (X := X) I a (SheafOfModules.sectionsMap e.inv s)) := by
      simp only [scaleFreeSection, Equiv.symm_apply_apply]

/- The chosen free coordinates are additive in the section.  These two
  identities let the projective-line pencil expose its actual coordinate pair
  without unfolding the sheaf-level trivialization each time. -/
theorem sectionCoordinateOfFreeIso_add
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (s t : E.sections) (i : I) :
    sectionCoordinateOfFreeIso (X := X) I e (addSections s t) i =
      sectionCoordinateOfFreeIso (X := X) I e s i +
        sectionCoordinateOfFreeIso (X := X) I e t i := by
  unfold sectionCoordinateOfFreeIso
  rw [sectionsMap_addSections e.inv s t]
  change freeSectionCoordinate (X := X) I
      (addFreeSections (X := X) I
        (SheafOfModules.sectionsMap e.inv s)
        (SheafOfModules.sectionsMap e.inv t)) i = _
  rw [freeSectionCoordinate_add]

theorem sectionCoordinateOfFreeIso_scale
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : E.sections) (i : I) :
    sectionCoordinateOfFreeIso (X := X) I e (scaleSection a s) i =
      unitEndomorphismValue (X := X) a *
        sectionCoordinateOfFreeIso (X := X) I e s i := by
  unfold sectionCoordinateOfFreeIso
  rw [sectionsMap_freeIso_inv_scaleSection, freeSectionCoordinate_scale]

/-- The zero ideal in a free trivialization is invariant under scaling the
section by an invertible scalar endomorphism. -/
theorem sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a]
    (s : E.sections) :
    sectionZeroIdealOfFreeIso (X := X) I e (scaleSection (X := X) a s) =
      sectionZeroIdealOfFreeIso (X := X) I e s := by
  unfold sectionZeroIdealOfFreeIso
  rw [sectionsMap_freeIso_inv_scaleSection I e a s]
  exact freeSectionZeroIdeal_scaleFreeSection_eq_of_isIso_global I a _

/-- The zero subscheme in a free trivialization is invariant under scaling
the section by an invertible scalar endomorphism. -/
theorem sectionZeroSubschemeOfFreeIso_scaleSection_eq_of_isIso
    [AlgebraicGeometry.IsAffine X] {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso a]
    (s : E.sections) :
    sectionZeroSubschemeOfFreeIso (X := X) I e (scaleSection (X := X) a s) =
      sectionZeroSubschemeOfFreeIso (X := X) I e s := by
  rw [sectionZeroSubschemeOfFreeIso, sectionZeroSubschemeOfFreeIso,
    sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso I e a s]

/-- The same overlap criterion for two free trivializations of one module
sheaf. -/
theorem sectionZeroIdealOfFreeIso_eq_of_coordinateSpan_eq
    {E : X.Modules} (I J : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (f : SheafOfModules.free (R := X.ringCatSheaf) J ≅ E)
    (s : E.sections)
    (h : Ideal.span (Set.range
      (sectionCoordinateOfFreeIso (X := X) I e s)) =
      Ideal.span (Set.range
        (sectionCoordinateOfFreeIso (X := X) J f s))) :
    sectionZeroIdealOfFreeIso (X := X) I e s =
      sectionZeroIdealOfFreeIso (X := X) J f s := by
  unfold sectionZeroIdealOfFreeIso
  apply (show freeSectionZeroIdeal (X := X) I
    (SheafOfModules.sectionsMap e.inv s) =
    freeSectionZeroIdeal (X := X) J
      (SheafOfModules.sectionsMap f.inv s) from ?_)
  unfold freeSectionZeroIdeal
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop h

/-- The overlap criterion for trivializations identifies the corresponding
scheme-theoretic zero loci as well. -/
theorem sectionZeroSubschemeOfFreeIso_eq_of_coordinateSpan_eq
    {E : X.Modules} (I J : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (f : SheafOfModules.free (R := X.ringCatSheaf) J ≅ E)
    (s : E.sections)
    (h : Ideal.span (Set.range
      (sectionCoordinateOfFreeIso (X := X) I e s)) =
      Ideal.span (Set.range
        (sectionCoordinateOfFreeIso (X := X) J f s))) :
    sectionZeroSubschemeOfFreeIso (X := X) I e s =
      sectionZeroSubschemeOfFreeIso (X := X) J f s := by
  rw [sectionZeroSubschemeOfFreeIso, sectionZeroSubschemeOfFreeIso,
    sectionZeroIdealOfFreeIso_eq_of_coordinateSpan_eq I J e f s h]

noncomputable def coordinateExpansion (I : Type u) [Fintype I] :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  ∑ i : I, freeCoordinateMap (X := X) I i ≫ SheafOfModules.ιFree i

theorem iota_comp_freeCoordinateMap (I : Type u) [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      freeCoordinateMap (X := X) I i =
      if j = i then 𝟙 _ else 0 := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
    (freeCoordinateMap (X := X) I i) j]
  unfold freeCoordinateMap
  rw [Equiv.apply_symm_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem coordinateExpansion_eq_id (I : Type u) [Fintype I] [DecidableEq I] :
    coordinateExpansion (X := X) I = 𝟙 _ := by
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _
  intro j
  change SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
    coordinateExpansion (X := X) I =
    SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ 𝟙 _
  rw [coordinateExpansion, Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single j]
  · rw [← Category.assoc, iota_comp_freeCoordinateMap (X := X) I]
    simp
  · intro b _ hb
    rw [← Category.assoc, iota_comp_freeCoordinateMap (X := X) I]
    simp [Ne.symm hb]
  · simp

noncomputable def freeTransitionCoefficient (I J : Type u)
    (m : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J)
    (i : I) (j : J) : Γ(X, ⊤) :=
  unitEndomorphismValue (X := X)
    (SheafOfModules.ιFree i ≫ m ≫ freeCoordinateMap (X := X) J j)

theorem unitEndomorphismValue_zero :
    unitEndomorphismValue (X := X) (0 :
      SheafOfModules.unit X.ringCatSheaf ⟶
        SheafOfModules.unit X.ringCatSheaf) = 0 := by
  simp only [unitEndomorphismValue, unitSectionAtTop,
    SheafOfModules.unitHomEquiv_apply_coe]
  rfl

theorem unitEndomorphismValue_sum {I : Type u} (t : I →
    (SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)) (s : Finset I) :
    unitEndomorphismValue (X := X) (∑ i ∈ s, t i) =
      ∑ i ∈ s, unitEndomorphismValue (X := X) (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitEndomorphismValue_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert, ha, not_false_eq_true,
      unitEndomorphismValue_add, ih]

theorem freeSectionCoordinate_sectionsMap (I J : Type u) [Fintype I] [DecidableEq I]
    (m : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (j : J) :
    freeSectionCoordinate (X := X) J (SheafOfModules.sectionsMap m s) j =
      ∑ i : I, freeSectionCoordinate (X := X) I s i *
        freeTransitionCoefficient (X := X) I J m i j := by
  let f : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) I :=
    (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm s
  have hmap : f ≫ m ≫ freeCoordinateMap (X := X) J j =
      ∑ i : I, (f ≫ freeCoordinateMap (X := X) I i) ≫
        (SheafOfModules.ιFree i ≫ m ≫ freeCoordinateMap (X := X) J j) := by
    calc
      f ≫ m ≫ freeCoordinateMap (X := X) J j =
          (f ≫ 𝟙 _) ≫ m ≫ freeCoordinateMap (X := X) J j := by simp
      _ = (f ≫ coordinateExpansion (X := X) I) ≫ m ≫
          freeCoordinateMap (X := X) J j := by rw [coordinateExpansion_eq_id]
      _ = ∑ i : I, (f ≫ freeCoordinateMap (X := X) I i) ≫
          (SheafOfModules.ιFree i ≫ m ≫ freeCoordinateMap (X := X) J j) := by
        rw [coordinateExpansion]
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  unfold freeSectionCoordinate freeTransitionCoefficient
  rw [← SheafOfModules.unitHomEquiv_symm_comp s m]
  change unitEndomorphismValue (X := X) (f ≫ m ≫ freeCoordinateMap (X := X) J j) = _
  rw [hmap, unitEndomorphismValue_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [unitEndomorphismValue_comp]
  rfl


/-- A change of finite free coordinates sends every coordinate into the ideal
of the original coordinates. -/
theorem freeSectionZeroIdeal_le_of_sectionsMap
    [AlgebraicGeometry.IsAffine X] (I J : Type u) [Fintype I] [DecidableEq I]
    (m : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) J)
    (s : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) :
    freeSectionZeroIdeal (X := X) J (SheafOfModules.sectionsMap m s) ≤
      freeSectionZeroIdeal (X := X) I s := by
  apply freeSectionZeroIdeal_le_of_coordinates_mem I J s
    (SheafOfModules.sectionsMap m s)
  intro j
  rw [freeSectionCoordinate_sectionsMap]
  apply Submodule.sum_mem
  intro i hi
  rw [mul_comm]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨i, rfl⟩

/-- For finite free trivializations, the coordinate ideal of a section is
independent of the chosen trivialization. -/
theorem sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
    [AlgebraicGeometry.IsAffine X] {E : X.Modules} (I J : Type u)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (g : SheafOfModules.free (R := X.ringCatSheaf) J ≅ E)
    (s : E.sections) :
    sectionZeroIdealOfFreeIso (X := X) I e s =
      sectionZeroIdealOfFreeIso (X := X) J g s := by
  apply le_antisymm
  · let m : SheafOfModules.free (R := X.ringCatSheaf) J ⟶
        SheafOfModules.free (R := X.ringCatSheaf) I := g.hom ≫ e.inv
    have hs : SheafOfModules.sectionsMap m
        (SheafOfModules.sectionsMap g.inv s) =
        SheafOfModules.sectionsMap e.inv s := by
      apply (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm.injective
      rw [← SheafOfModules.unitHomEquiv_symm_comp
        (SheafOfModules.sectionsMap g.inv s) m]
      rw [← SheafOfModules.unitHomEquiv_symm_comp s g.inv]
      rw [← SheafOfModules.unitHomEquiv_symm_comp s e.inv]
      dsimp [m]
      calc
        ((SheafOfModules.unitHomEquiv E).symm s ≫ g.inv) ≫ g.hom ≫ e.inv =
            ((SheafOfModules.unitHomEquiv E).symm s ≫ g.inv) ≫
              (g.hom ≫ e.inv) := Category.assoc _ _ _
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫
            (g.inv ≫ (g.hom ≫ e.inv)) := Category.assoc _ _ _
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫
            ((g.inv ≫ g.hom) ≫ e.inv) := by
              exact congrArg (fun q => (SheafOfModules.unitHomEquiv E).symm s ≫ q)
                (Category.assoc g.inv g.hom e.inv).symm
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫ e.inv := by
          rw [g.inv_hom_id]
          exact congrArg (fun q => (SheafOfModules.unitHomEquiv E).symm s ≫ q)
            (Category.id_comp e.inv)
    unfold sectionZeroIdealOfFreeIso
    rw [← hs]
    exact freeSectionZeroIdeal_le_of_sectionsMap J I m
      (SheafOfModules.sectionsMap g.inv s)
  · let m : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
        SheafOfModules.free (R := X.ringCatSheaf) J := e.hom ≫ g.inv
    have hs : SheafOfModules.sectionsMap m
        (SheafOfModules.sectionsMap e.inv s) =
        SheafOfModules.sectionsMap g.inv s := by
      apply (SheafOfModules.free (R := X.ringCatSheaf) J).unitHomEquiv.symm.injective
      rw [← SheafOfModules.unitHomEquiv_symm_comp
        (SheafOfModules.sectionsMap e.inv s) m]
      rw [← SheafOfModules.unitHomEquiv_symm_comp s e.inv]
      rw [← SheafOfModules.unitHomEquiv_symm_comp s g.inv]
      dsimp [m]
      calc
        ((SheafOfModules.unitHomEquiv E).symm s ≫ e.inv) ≫ e.hom ≫ g.inv =
            ((SheafOfModules.unitHomEquiv E).symm s ≫ e.inv) ≫
              (e.hom ≫ g.inv) := Category.assoc _ _ _
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫
            (e.inv ≫ (e.hom ≫ g.inv)) := Category.assoc _ _ _
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫
            ((e.inv ≫ e.hom) ≫ g.inv) := by
              exact congrArg (fun q => (SheafOfModules.unitHomEquiv E).symm s ≫ q)
                (Category.assoc e.inv e.hom g.inv).symm
        _ = (SheafOfModules.unitHomEquiv E).symm s ≫ g.inv := by
          rw [e.inv_hom_id]
          exact congrArg (fun q => (SheafOfModules.unitHomEquiv E).symm s ≫ q)
            (Category.id_comp g.inv)
    unfold sectionZeroIdealOfFreeIso
    rw [← hs]
    exact freeSectionZeroIdeal_le_of_sectionsMap I J m
      (SheafOfModules.sectionsMap e.inv s)

/-- The associated finite-free zero subscheme is likewise independent of the
chosen trivialization. -/
theorem sectionZeroSubschemeOfFreeIso_eq_of_finiteFreeIso
    [AlgebraicGeometry.IsAffine X] {E : X.Modules} (I J : Type u)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (g : SheafOfModules.free (R := X.ringCatSheaf) J ≅ E)
    (s : E.sections) :
    sectionZeroSubschemeOfFreeIso (X := X) I e s =
      sectionZeroSubschemeOfFreeIso (X := X) J g s := by
  rw [sectionZeroSubschemeOfFreeIso, sectionZeroSubschemeOfFreeIso,
    sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso I J e g s]


/-- Free modules over an open subscheme are transported through the equivalence
between modules over the over-site and modules on the open subscheme. -/
noncomputable def overEquivFreeIso (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let E := AlgebraicGeometry.Scheme.Modules.overEquiv U
  letI : PreservesColimitsOfSize.{u, u} E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits
  letI hpres : PreservesColimitsOfShape (Discrete I) E.functor :=
    PreservesColimitsOfSize.preservesColimitsOfShape
  let η : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅
      E.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm
  exact (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ E.functor I hpres η)

/-- Restrict a global module section to an open subscheme, expressed as a
section of the corresponding module on that subscheme. -/
noncomputable def restrictSectionToOpen {E : X.Modules} (U : X.Opens)
    (s : E.sections) :
    ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U)).sections :=
  ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv
    ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.map
      ((E.unitHomEquiv.symm s).over U))

/-- A free presentation over an open subset gives a genuine free
trivialization of the corresponding module on its open subscheme. -/
noncomputable def localFreeIsoOfOver {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) :
    SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U) :=
  overEquivFreeIso (X := X) U I ≪≫
    (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.mapIso t

/-- The zero ideal of a global section on a chosen free open trivialization. -/
noncomputable def localSectionZeroIdealOfOver {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) : AlgebraicGeometry.Scheme.IdealSheafData (U : Scheme.{u}) :=
  sectionZeroIdealOfFreeIso I (localFreeIsoOfOver (X := X) U I t)
    (restrictSectionToOpen (X := X) U s)

/-- The corresponding local scheme-theoretic zero locus. -/
noncomputable def localSectionZeroSubschemeOfOver {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) : Scheme.{u} :=
  (localSectionZeroIdealOfOver (X := X) U I t s).subscheme

/-- The zero ideal of a section already restricted to an open trivialization.
This is the local form needed when the scalar relating two homogeneous
coordinate charts is a unit only on their overlap. -/
noncomputable def zeroIdealOfLocalSectionOfOver {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj
      (E.over U)).sections) : AlgebraicGeometry.Scheme.IdealSheafData (U : Scheme.{u}) :=
  sectionZeroIdealOfFreeIso I (localFreeIsoOfOver (X := X) U I t) s

/-- A local-section zero ideal is invariant under an invertible local scalar.
Unlike the global version, this works with the scalar defined directly on the
open subscheme. -/
theorem zeroIdealOfLocalSectionOfOver_scaleSection_eq_of_isIso
    {E : X.Modules} (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (a : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) [IsIso a]
    (s : ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj
      (E.over U)).sections) :
    zeroIdealOfLocalSectionOfOver (X := X) U I t
      (scaleSection (X := (U : Scheme.{u})) a s) =
    zeroIdealOfLocalSectionOfOver (X := X) U I t s := by
  unfold zeroIdealOfLocalSectionOfOver
  exact sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso I
    (localFreeIsoOfOver (X := X) U I t) a s

/-- The local zero ideal obtained from a global section agrees with the same
construction applied to its explicitly restricted section. -/
theorem localSectionZeroIdealOfOver_eq_zeroIdealOfLocalSectionOfOver
    {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) :
    localSectionZeroIdealOfOver (X := X) U I t s =
      zeroIdealOfLocalSectionOfOver (X := X) U I t
        (restrictSectionToOpen (X := X) U s) := rfl

/-- If restriction identifies a globally scaled section with a locally
scaled one, its local zero ideal is unchanged.  This packages the exact
compatibility used on the overlap of the two projective-line charts. -/
theorem localSectionZeroIdealOfOver_scaleSection_eq_of_localCompatibility
    {E : X.Modules} (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) [IsIso a]
    (s : E.sections)
    (hcompat : restrictSectionToOpen (X := X) U
      (scaleSection (X := X) c s) =
        scaleSection (X := (U : Scheme.{u})) a
          (restrictSectionToOpen (X := X) U s)) :
    localSectionZeroIdealOfOver (X := X) U I t
      (scaleSection (X := X) c s) =
      localSectionZeroIdealOfOver (X := X) U I t s := by
  rw [localSectionZeroIdealOfOver_eq_zeroIdealOfLocalSectionOfOver,
    localSectionZeroIdealOfOver_eq_zeroIdealOfLocalSectionOfOver, hcompat]
  exact zeroIdealOfLocalSectionOfOver_scaleSection_eq_of_isIso U I t a _

/-- The closed immersion of the local zero locus into its open subscheme. -/
noncomputable def localSectionZeroSubschemeOfOverι {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) : localSectionZeroSubschemeOfOver (X := X) U I t s ⟶
      (U : Scheme.{u}) :=
  (localSectionZeroIdealOfOver (X := X) U I t s).subschemeι

/-- Each local zero locus is a scheme-theoretic closed subscheme of its
chosen open chart. -/
theorem isClosedImmersion_localSectionZeroSubschemeOfOverι
    {E : X.Modules} (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) :
    IsClosedImmersion (localSectionZeroSubschemeOfOverι (X := X) U I t s) := by
  change IsClosedImmersion (localSectionZeroIdealOfOver (X := X) U I t s).subschemeι
  infer_instance

/-- On an affine open, the local zero ideal does not depend on the chosen
finite free trivialization. -/
theorem localSectionZeroIdealOfOver_eq_of_finiteFreeIso
    {E : X.Modules} (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ E.over U)
    (s : E.sections) :
    localSectionZeroIdealOfOver (X := X) U I t s =
      localSectionZeroIdealOfOver (X := X) U J v s := by
  unfold localSectionZeroIdealOfOver
  exact sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso I J
    (localFreeIsoOfOver (X := X) U I t)
    (localFreeIsoOfOver (X := X) U J v)
    (restrictSectionToOpen (X := X) U s)

/-- The local zero schemes are also independent of the chosen finite free
trivialization on an affine open. -/
theorem localSectionZeroSubschemeOfOver_eq_of_finiteFreeIso
    {E : X.Modules} (U : X.Opens) [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ E.over U)
    (s : E.sections) :
    localSectionZeroSubschemeOfOver (X := X) U I t s =
      localSectionZeroSubschemeOfOver (X := X) U J v s := by
  rw [localSectionZeroSubschemeOfOver, localSectionZeroSubschemeOfOver,
    localSectionZeroIdealOfOver_eq_of_finiteFreeIso U I J t v s]


/-- Restrict a finite free trivialization along an inclusion of open subsets.
The resulting presentation is still a literal finite free presentation of the
restricted module. -/
noncomputable def restrictFreeIsoOver {U V : X.Opens} (f : V ⟶ U) (I : Type u)
    {E : X.Modules}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over V) I ≅ E.over V := by
  let F := SheafOfModules.overMap X.ringCatSheaf f
  letI hpres : PreservesColimitsOfShape (Discrete I) F := inferInstance
  let η : SheafOfModules.unit (X.ringCatSheaf.over V) ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (SheafOfModules.overMapUnitIso f).symm
  exact (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hpres η) ≪≫
    F.mapIso t ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf f).app E

/-- On a smaller affine open, the zero ideal obtained by restricting a free
trivialization agrees with that from any other finite free trivialization.
This is the overlap equality needed to glue the local zero loci of the Serre
pencil. -/
theorem localSectionZeroIdealOfOver_restrictFreeIsoOver_eq
    {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over V) J ≅ E.over V)
    (s : E.sections) :
    localSectionZeroIdealOfOver (X := X) V I
      (restrictFreeIsoOver (X := X) f I t) s =
      localSectionZeroIdealOfOver (X := X) V J v s := by
  exact localSectionZeroIdealOfOver_eq_of_finiteFreeIso V I J
    (restrictFreeIsoOver (X := X) f I t) v s

/-- The same overlap equality for the associated local closed subschemes. -/
theorem localSectionZeroSubschemeOfOver_restrictFreeIsoOver_eq
    {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over V) J ≅ E.over V)
    (s : E.sections) :
    localSectionZeroSubschemeOfOver (X := X) V I
      (restrictFreeIsoOver (X := X) f I t) s =
      localSectionZeroSubschemeOfOver (X := X) V J v s := by
  rw [localSectionZeroSubschemeOfOver, localSectionZeroSubschemeOfOver,
    localSectionZeroIdealOfOver_restrictFreeIsoOver_eq f I J t v s]


/-- The scalar endomorphism induced on the source by pullback.  It is
conjugated by the canonical comparison of the two unit modules. -/
noncomputable def pullbackUnitEndomorphism {Y : Scheme.{u}} (f : X ⟶ Y)
    (hunit : IsIso (pullbackUnitComparison f))
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf := by
  exact Classical.choose hunit.out ≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).map a ≫
      pullbackUnitComparison f

/-- Pullback preserves the identity scalar endomorphism. -/
theorem pullbackUnitEndomorphism_id {Y : Scheme.{u}} (f : X ⟶ Y)
    (hunit : IsIso (pullbackUnitComparison f)) :
    pullbackUnitEndomorphism f hunit (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  unfold pullbackUnitEndomorphism
  have hchoose : Classical.choose hunit.out = inv (pullbackUnitComparison f) := by
    congr 1
  erw [hchoose]
  let F := AlgebraicGeometry.Scheme.Modules.pullback f
  have hmap : F.map (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) =
      𝟙 (F.obj (SheafOfModules.unit Y.ringCatSheaf)) := F.map_id _
  erw [hmap]
  exact IsIso.inv_hom_id_assoc (pullbackUnitComparison f) (𝟙 _)

/-- Pullback commutes with scalar multiplication of a module section. -/
theorem pullbackSection_scaleSection {Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules}
    (hunit : IsIso (pullbackUnitComparison f))
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf) (s : E.sections) :
    pullbackSection f E hunit (scaleSection a s) =
      scaleSection (pullbackUnitEndomorphism f hunit a)
        (pullbackSection f E hunit s) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  apply ((AlgebraicGeometry.Scheme.Modules.pullback f).obj E).unitHomEquiv.symm.injective
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  unfold scaleSection
  simp only [Equiv.symm_apply_apply]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  unfold pullbackUnitEndomorphism
  have hchoose : Classical.choose hunit.out = inv (pullbackUnitComparison f) := by
    congr 1
  erw [hchoose]
  let F := AlgebraicGeometry.Scheme.Modules.pullback f
  let p := pullbackUnitComparison f
  let m := E.unitHomEquiv.symm s
  change inv p ≫ F.map (a ≫ m) =
    (inv p ≫ F.map a ≫ p) ≫ inv p ≫ F.map m
  have hmap : F.map (a ≫ m) = F.map a ≫ F.map m := F.map_comp a m
  rw [hmap]
  calc
    inv p ≫ F.map a ≫ F.map m =
      inv p ≫ F.map a ≫ (𝟙 _ ≫ F.map m) := by
      exact congrArg (fun q => inv p ≫ F.map a ≫ q)
        (Category.id_comp _).symm
    _ = (inv p ≫ F.map a ≫ 𝟙 _) ≫ F.map m := by
      exact (Category.assoc _ _ _).symm
    _ = (inv p ≫ F.map a ≫ (p ≫ inv p)) ≫ F.map m := by
      exact congrArg (fun q => (inv p ≫ F.map a ≫ q) ≫ F.map m)
        (IsIso.hom_inv_id p).symm
    _ = (inv p ≫ F.map a ≫ p) ≫ inv p ≫ F.map m := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun q => inv p ≫ q) (Category.assoc _ _ _))

/-- Pullback transports a two-term scalar linear combination by pulling back
each section and conjugating each scalar through the unit comparison. -/
theorem pullbackSection_linearCombination {Y : Scheme.{u}} (f : X ⟶ Y)
    {E : Y.Modules} (hunit : IsIso (pullbackUnitComparison f))
    (a b : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf)
    (s t : E.sections) :
    pullbackSection f E hunit
      (addSections (scaleSection a s) (scaleSection b t)) =
    addSections
      (scaleSection (pullbackUnitEndomorphism f hunit a)
        (pullbackSection f E hunit s))
      (scaleSection (pullbackUnitEndomorphism f hunit b)
        (pullbackSection f E hunit t)) := by
  rw [pullbackSection_addSections, pullbackSection_scaleSection,
    pullbackSection_scaleSection]


end PfaffianDescent.BundleSectionZeroLocus
