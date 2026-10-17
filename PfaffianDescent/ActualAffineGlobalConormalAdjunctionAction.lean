import PfaffianDescent.ActualGlobalClosedConormalDifferentialMap
import PfaffianDescent.ActualAffineSheafPointClass

/- SOURCE ONLY / UNVERIFIED. The GENUINE GLOBAL map has this affine
point-section action by the actual adjunction unit and Gamma-pushforward
naturality. No equality with a prescribed tensor map is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

lemma actualAffineGlobalConormalAdjunctionAction
    (rho : R →+* L) [IsClosedImmersion (Spec.map (CommRingCat.ofHom rho))]
    (m : (moduleSpecΓFunctor (R := .of R)).obj
      (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom rho)))
      (actualAffineSheafPointClass (CommRingCat.ofHom rho)
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho))) m) =
    actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
        ((closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom rho))).val.app
          (op ⊤) m)) := by
  let phi := CommRingCat.ofHom rho
  let q := Spec.map phi
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let J : (Spec (.of R)).Modules := closedImmersionModule q
  let O : (Spec (.of R)).Modules := schemeRelativeDifferentials g
  let P := Scheme.Modules.pullback q
  let Q := Scheme.Modules.pushforward q
  let G : (Spec (.of R)).Modules ⥤ ModuleCat R :=
    moduleSpecΓFunctor (R := .of R)
  let Gpoint : (Spec (.of L)).Modules ⥤ ModuleCat L :=
    moduleSpecΓFunctor (R := .of L)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q
  let d : P.obj J ⟶ P.obj O := actualGlobalClosedConormalDifferentialMap g q
  let N := affineGammaPushforwardNatIso phi
  have hd : adj.unit.app J ≫ Q.map d =
      actualClosedImmersionIdealUniversalDifferentialPushforward g q :=
    (adj.homEquiv_unit J (P.obj O) d).symm.trans
      (actualGlobalClosedConormalDifferentialMap_adjunct g q)
  have hn := N.hom.naturality d
  change Gpoint.map (X := P.obj J) (Y := P.obj O) d (N.hom.app (P.obj J) (G.map (adj.unit.app J) m)) = _
  calc
    Gpoint.map (X := P.obj J) (Y := P.obj O) d (N.hom.app (P.obj J) (G.map (adj.unit.app J) m)) =
        N.hom.app (P.obj O)
          (G.map (Q.map d) (G.map (adj.unit.app J) m)) := by
      have h := ConcreteCategory.congr_hom hn (G.map (adj.unit.app J) m)
      exact h.symm
    _ = N.hom.app (P.obj O)
        (G.map (actualClosedImmersionIdealUniversalDifferentialPushforward g q) m) := by
      have hmap := (G.map_comp (adj.unit.app J) (Q.map d)).symm.trans
        (congrArg (fun a : J ⟶ Q.obj (P.obj O) => G.map a) hd)
      have hvalue := ConcreteCategory.congr_hom hmap m
      exact congrArg
        (fun z : G.obj (Q.obj (P.obj O)) => N.hom.app (P.obj O) z) hvalue
    _ = _ := rfl

end PfaffianDescent
