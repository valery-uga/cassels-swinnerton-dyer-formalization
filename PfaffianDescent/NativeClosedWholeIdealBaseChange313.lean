import PfaffianDescent.FiniteFlatHilbertTestPoints195
import PfaffianDescent.NativeAmbientPullbackChart300

/-! SOURCE ONLY313. Whole ideal image under closed embedding commutes with
genuine Cartesian base change. No support comparison is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma nativeClosedWholeIdeal_map_comap313 {Z0 Z X0 X : Scheme.{u}}
    (dZ : Z0 ⟶ Z) (j0 : Z0 ⟶ X0) (j : Z ⟶ X) (dX : X0 ⟶ X)
    [IsClosedImmersion j] (H : IsPullback dZ j0 j dX) (Q : Z.IdealSheafData) :
    (Q.comap dZ).map j0 = (Q.map j).comap dX := by
  let L := Q.comap dZ
  let e := Q.comapIso dZ
  let r := e.hom ≫ pullback.snd dZ Q.subschemeι
  have Hinner : IsPullback r L.subschemeι Q.subschemeι dZ := by
    change IsPullback ((Q.comapIso dZ).hom ≫ pullback.snd dZ Q.subschemeι)
      (Q.comap dZ).subschemeι Q.subschemeι dZ
    simpa only [Scheme.IdealSheafData.comapIso_hom_fst] using
      (nativePullbackDomainIso300 (IsPullback.of_hasPullback dZ Q.subschemeι).flip
        (Q.comapIso dZ))
  have Houter : IsPullback r (L.subschemeι ≫ j0) (Q.subschemeι ≫ j) dX :=
    Hinner.paste_vert H
  exact (wholeIdeal_comap_eq_of_isPullback195 r (L.subschemeι ≫ j0)
    (Q.subschemeι ≫ j) dX Houter).symm

end PfaffianDescent
end
