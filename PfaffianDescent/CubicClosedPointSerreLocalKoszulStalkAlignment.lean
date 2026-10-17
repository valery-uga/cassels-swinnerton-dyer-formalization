import PfaffianDescent.CubicClosedPointSerreLocalKoszulStalkFree
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodOriginalStalkLift
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodStalkLiftIso

/-! # The actual free-source stalk lift of the original Serre extension -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
universe u

theorem cubicClosedPointSerreLocalKoszulFreeLastOnOpen_eq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (s : CubicClosedPointSerreLocalKoszulData i T U q f eT) :
    cubicClosedPointSerreLocalKoszulFreeLastOnOpen i T U q f eT s =
      (cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso U).hom ≫ s.last := by
  simp only [cubicClosedPointSerreLocalKoszulFreeLastOnOpen,
    cubicClosedPointSerreLocalKoszulRepresenterPairFreeIso,
    cubicClosedPointSerreLocalKoszulLastOnRepresenter,
    cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- Actual native stalk freeness gives a lift of the constructed two-generator
quotient whose entire original stalk map is an isomorphism. The ideal
coordinate and the projection square are constructed from the actual
source sequence and its actual ideal inclusion. -/
theorem cubicClosedPointSerreLocalKoszul_exists_stalk_lift
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (s : CubicClosedPointSerreLocalKoszulData i T U q f eT) (x : U)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    [Module.Free (X.presheaf.stalk (U.ι x)) ((schemeModuleStalkModuleFunctor X (U.ι x)).obj e.E)]
    (hqreg : X.presheaf.germ U (U.ι x) x.2 q ∈ (X.presheaf.stalk (U.ι x))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U (U.ι x) x.2 q})
      (X.presheaf.germ U (U.ι x) x.2 f) ∈
      ((X.presheaf.stalk (U.ι x)) ⧸ Ideal.span {X.presheaf.germ U (U.ι x) x.2 q})⁰)
    (hmax : Ideal.span ({X.presheaf.germ U (U.ι x) x.2 q,
      X.presheaf.germ U (U.ι x) x.2 f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι x))) :
    ∃ l : (schemeModuleStalkModuleFunctor X (U.ι x)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj e.E,
      l.hom ≫ (schemeModuleStalkModuleFunctor X (U.ι x)).map e.projection =
        cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
          (closedImmersionIdealTwist i T)
          ((cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso U).hom ≫ s.last) := by
  let R := X.presheaf.stalk (U.ι x)
  let F := schemeModuleStalkModuleFunctor X (U.ι x)
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let S := e.complex.map F
  have hS : S.ShortExact := e.shortExact.map_of_exact F
  let q₀ := X.presheaf.germ U (U.ι x) x.2 q
  let f₀ := X.presheaf.germ U (U.ι x) x.2 f
  obtain ⟨a, _, hqa⟩ := cubicClosedPointSerreLocalKoszulFree_exists_idealCoordinate
    i T U q f eT s x
  let n := schemeModuleUnitStalkIso X (U.ι x)
  let ι : R →ₗ[R] F.obj e.E := (F.map e.inclusion).hom.comp n.inv.hom
  let π : F.obj e.E →ₗ[R] Ideal.span ({q₀, f₀} : Set R) :=
    a.hom.hom.comp (F.map e.projection).hom
  have hraw : Function.Exact (F.map e.inclusion) (F.map e.projection) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
  have hex : Function.Exact ι π := by
    have hpre := functionExact_precomp_of_surjective (F.map e.inclusion) n.inv
      (F.map e.projection) hraw n.symm.toLinearEquiv.surjective
    exact hpre.comp_injective a.hom a.toLinearEquiv.injective (map_zero _)
  have hinj : Function.Injective ι :=
    ((ModuleCat.mono_iff_injective (F.map e.inclusion)).mp hS.mono_f).comp
      n.symm.toLinearEquiv.injective
  have hsurj : Function.Surjective π := a.toLinearEquiv.surjective.comp
    ((ModuleCat.epi_iff_surjective (F.map e.projection)).mp hS.epi_g)
  have hqm : q₀ ∈ IsLocalRing.maximalIdeal R := hmax ▸ Ideal.subset_span (by simp [q₀])
  have hfm : f₀ ∈ IsLocalRing.maximalIdeal R := hmax ▸ Ideal.subset_span (by simp [f₀])
  obtain ⟨l₀, hl₀⟩ := cubicClosedPointSerreFreeNeighborhood_exists_stalk_lift_iso
    ι q₀ f₀ π hex hinj hsurj hqreg hfreg hqm hfm
  let c := cubicClosedPointSerreLocalKoszulFreeNativeCoordinate U x
  let b := l₀.toModuleIso
  let l := c ≪≫ b
  have hb : b.hom ≫ F.map e.projection ≫ a.hom = ModuleCat.ofHom (localKoszulToIdeal q₀ f₀) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact hl₀ z
  have hl : l.hom ≫ F.map e.projection =
      cubicClosedPointSerreLocalKoszulFreeLastNative i T U q f eT s x := by
    apply (cancel_mono a.hom).mp
    apply (cancel_epi c.inv).mp
    change c.inv ≫ (c.hom ≫ b.hom) ≫ F.map e.projection ≫ a.hom =
      c.inv ≫ cubicClosedPointSerreLocalKoszulFreeLastNative i T U q f eT s x ≫ a.hom
    simp only [Category.assoc, c.inv_hom_id_assoc]
    exact hb.trans hqa.symm
  refine ⟨l, ?_⟩
  rw [hl]
  simp only [cubicClosedPointSerreLocalKoszulFreeLastNative,
    cubicClosedPointSerreLocalKoszulFreeLastOnOpen_eq]

end PfaffianDescent
