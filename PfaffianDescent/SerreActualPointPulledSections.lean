import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree

/-! Actual pulled global sections and native point Gamma composition
preserve literal section evaluation. No global-sections comparison is assumed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreActualPulledGlobalSection
    {F L : Type u} [Field F] [Field L] {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of F)) (base' : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    SchemeModuleGlobalSectionsOver base' ((Scheme.Modules.pullback f).obj M) :=
  ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
    (pullbackSection f M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s))

def serreActualPointPulledGammaEquiv
    {E : Type u} [Field E] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (r : Spec (.of E) ⟶ Y) (q : Spec (.of E) ⟶ X)
    (hq : r ≫ f = q) (M : X.Modules) :
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback f).obj M)) ≃ₗ[E]
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback q).obj M) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of E)).mapIso
    ((Scheme.Modules.pullbackComp r f).app M ≪≫
      (Scheme.Modules.pullbackCongr hq).app M)).toLinearEquiv

def serreActualThreePointPulledGammaEquiv
    {E : Type u} [Field E] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (r : Fin 3 → (Spec (.of E) ⟶ Y))
    (q : Fin 3 → (Spec (.of E) ⟶ X))
    (hq : ∀ i, r i ≫ f = q i) (M : X.Modules) :
    (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (r i)).obj ((Scheme.Modules.pullback f).obj M))) ≃ₗ[E]
    (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (q i)).obj M)) :=
  LinearEquiv.piCongrRight (fun i => serreActualPointPulledGammaEquiv f (r i) (q i) (hq i) M)

theorem serreActualThreePointPulledGammaEquiv_one_tmul
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F E] [Algebra L E]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of F)) (base' : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (r : Fin 3 → (Spec (.of E) ⟶ Y))
    (q : Fin 3 → (Spec (.of E) ⟶ X))
    (hq : ∀ i, r i ≫ f = q i)
    (hr : ∀ i, r i ≫ base' = Spec.map (CommRingCat.ofHom (algebraMap L E)))
    (hqb : ∀ i, q i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    serreActualThreePointPulledGammaEquiv f r q hq M
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base' r hr ((Scheme.Modules.pullback f).obj M)
        (1 ⊗ₜ[L] serreActualPulledGlobalSection base base' f M s)) =
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base q hqb M
      (1 ⊗ₜ[F] s) := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul,
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  funext i
  have hs := sectionsMap_pullbackComp_pullbackCongr_pullbackSection
    (r i) f (q i) (hq i) M (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _)
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)
  have hv := congrArg (fun t => t.val (op ⊤)) hs
  simp only [serreActualThreePointPulledGammaEquiv, LinearEquiv.piCongrRight_apply,
    serreActualPointPulledGammaEquiv, serreActualPulledGlobalSection, Equiv.apply_symm_apply]
  change ((moduleSpecΓFunctor (R := CommRingCat.of E)).map
      ((Scheme.Modules.pullbackComp (r i) f).app M ≪≫
        (Scheme.Modules.pullbackCongr (hq i)).app M).hom).hom
      ((pullbackSection (r i) ((Scheme.Modules.pullback f).obj M)
        (isIso_pullbackUnitComparison _)
        (pullbackSection f M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s))).val (op ⊤)) = _
  exact hv

end PfaffianDescent
