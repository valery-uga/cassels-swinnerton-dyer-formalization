import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernel
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {A B K : Type u} [CommRing A] [CommRing B] [Field K]
set_option backward.isDefEq.respectTransparency false

private theorem nativeUnitGammaSquare :
    ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app (ModuleCat.of A A)) ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (affineGlobalSectionsUnitTildeIso (A := A)).hom =
    (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom := by
  rw [affineGlobalSectionsUnitTildeIso_hom_eq_tildeSelf]
  change _ ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (𝟙 _) = _
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    (affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit (A := A)).symm

/-- The canonical native H coordinate on sections of the ACTUAL affine closed ideal.
Its inclusion compatibility follows from the direct kernelIso construction. -/
def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))] :
    RingHom.ker g ≃ₗ[A]
      (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g))) :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).app
    (ModuleCat.of A (RingHom.ker g))).toLinearEquiv ≪≫ₗ
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso g)).toLinearEquiv

/-- Actual point-pullback Gamma coordinates use the SAME inclusion-compatible native H. -/
def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (r : A →+* K) :
    letI : Algebra A K := r.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom r))).obj
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))) ≃ₗ[K]
      K ⊗[A] RingHom.ker g := by
  letI : Algebra A K := r.toAlgebra
  exact ((moduleSpecΓFunctor (R := CommRingCat.of K)).mapIso
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom r))).mapIso
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso g).symm)).toLinearEquiv ≪≫ₗ
    cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv r _

/-- The literal actual ideal global section attached to h has actual structure coefficient h. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv_toUnit
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (a : RingHom.ker g) :
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)))).hom
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a) =
    (affineGlobalSectionsUnitLinearEquiv (A := A)).symm a.1 := by
  let R := CommRingCat.of A
  let G := moduleSpecΓFunctor (R := R)
  let e := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso g
  let H := ModuleCat.of A (RingHom.ker g)
  let u := (tilde.toTildeΓNatIso (R := R)).hom
  have he := congrArg (fun f => G.map f)
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso_hom_toUnit g)
  rw [Functor.map_comp, Functor.map_comp] at he
  have hn := u.naturality (ModuleCat.ofHom (RingHom.ker g).subtype)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hmaps : u.app H ≫ G.map e.hom ≫
      G.map (IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g))) =
      ModuleCat.ofHom (RingHom.ker g).subtype ≫
        (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom := by
    rw [he, ← Category.assoc, ← hn, Category.assoc]
    exact congrArg (fun t => ModuleCat.ofHom (RingHom.ker g).subtype ≫ t)
      (nativeUnitGammaSquare (A := A))
  exact congrArg (fun f => f.hom a) hmaps

/-- The ACTUAL ideal-section restriction to an ACTUAL point fibre is 1 tensor h,
with the SAME canonical H coordinate on both sides. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealPointEvaluation_apply
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (r : A →+* K) (a : RingHom.ker g) :
    letI : Algebra A K := r.toAlgebra
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv g r
      ((cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
        (CommRingCat.ofHom r)
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))).hom
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a)) =
    1 ⊗ₜ[A] a := by
  letI : Algebra A K := r.toAlgebra
  let e := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso g
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom r))
  let G := moduleSpecΓFunctor (R := CommRingCat.of K)
  let ep := G.mapIso (P.mapIso e)
  have hn := cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_naturality
    (CommRingCat.ofHom r) e.hom
  have hna := congrArg (fun f => f.hom
    (((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app
      (ModuleCat.of A (RingHom.ker g))).hom a)) hn
  change
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom r) _).hom
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a) =
    ep.hom ((cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap
      r (RingHom.ker g)).hom a) at hna
  rw [hna]
  change cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv r (RingHom.ker g)
    (ep.inv (ep.hom ((cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap
      r (RingHom.ker g)).hom a))) = _
  rw [Iso.hom_inv_id_apply]
  exact cubicClosedPointSerreSurfaceJetCotangent_affineIdealPointEvaluationMap_apply r _ a

end PfaffianDescent
