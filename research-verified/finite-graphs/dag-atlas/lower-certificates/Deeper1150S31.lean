import AtlasCut

namespace CutWords1150
open AtlasLower AtlasMemo
set_option maxRecDepth 14000
set_option maxHeartbeats 9500000

def s31 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]

private def z31c0 : State := [0x408102040810200000000000000, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e0 : optimized 6 0 z31c0 = false := by decide +kernel

private def z31c1 : State := [0x40810204081020003f800003f80, 0x183060c183060c00000000000000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e1 : optimized 6 0 z31c1 = false := by decide +kernel

private def z31c2 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x8102040810204000000000000000, 0xa142850a1428500000000000007f]
private theorem e2 : optimized 6 0 z31c2 = false := by decide +kernel

private def z31c3 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e3 : optimized 6 0 z31c3 = false := by decide +kernel

private def z31c4 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x850a142850a142fffffff0003f80, 0xa142850a1428500000000000007f]
private theorem e4 : optimized 6 0 z31c4 = false := by decide +kernel

private def z31c5 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x993264c993264cffffffffffc000, 0xa142850a1428500000000000007f]
private theorem e5 : optimized 6 0 z31c5 = false := by decide +kernel

private def z31c6 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e6 : optimized 6 0 z31c6 = false := by decide +kernel

private def z31c7 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xe1c3870e1c3870ffffffffffff80]
private theorem e7 : optimized 6 0 z31c7 = false := by decide +kernel

private def z31c8 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x64c993264c99320003f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e8 : optimized 6 0 z31c8 = false := by decide +kernel

private def z31c9 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x78f1e3c78f1e3cfffc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e9 : optimized 6 0 z31c9 = false := by decide +kernel

private def z31c10 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e10 : optimized 6 0 z31c10 = false := by decide +kernel

private def z31c11 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e11 : optimized 6 1 z31c11 = false := by decide +kernel

private def z31c12 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xbf7efdfbf7efdf0000000000007f]
private theorem e12 : optimized 6 0 z31c12 = false := by decide +kernel

private def z31c13 : State := [0x40810204081020003f800003f80, 0x183060c183060cfffc000fffc000, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e13 : optimized 6 1 z31c13 = false := by decide +kernel

private def z31c14 : State := [0x40810204081020003f800003f80, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e14 : optimized 6 0 z31c14 = false := by decide +kernel

private def z31c15 : State := [0x40810204081020003f800003f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x5ab56ad5ab56adfffc07ffffc000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e15 : optimized 6 0 z31c15 = false := by decide +kernel

private def z31c16 : State := [0x40810204081020003f800003f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x78f1e3c78f1e3cfffc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e16 : optimized 6 0 z31c16 = false := by decide +kernel

private def z31c17 : State := [0x40810204081020003f800003f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x993264c993264cffffffffffc000, 0xa142850a1428500000000000007f]
private theorem e17 : optimized 6 0 z31c17 = false := by decide +kernel

private def z31c18 : State := [0x40810204081020003f800003f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x993264c993264cffffffffffc000, 0xa142850a1428500000000000007f]
private theorem e18 : optimized 6 1 z31c18 = false := by decide +kernel

private def z31c19 : State := [0x40810204081020003f800003f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x78f1e3c78f1e3cfffc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e19 : optimized 6 1 z31c19 = false := by decide +kernel

private def z31c20 : State := [0x183060c183060cfffc000fffc000, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e20 : optimized 6 0 z31c20 = false := by decide +kernel

private def z31c21 : State := [0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x468d1a3468d1a30003fff0003f80, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e21 : optimized 6 0 z31c21 = false := by decide +kernel

private def z31c22 : State := [0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x64c993264c99320003f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e22 : optimized 6 0 z31c22 = false := by decide +kernel

private def z31c23 : State := [0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x850a142850a142fffffff0003f80, 0xa142850a1428500000000000007f]
private theorem e23 : optimized 6 0 z31c23 = false := by decide +kernel

private def z31c24 : State := [0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x850a142850a142fffffff0003f80, 0xa142850a1428500000000000007f]
private theorem e24 : optimized 6 1 z31c24 = false := by decide +kernel

private def z31c25 : State := [0x183060c183060cfffc000fffc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x64c993264c99320003f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e25 : optimized 6 1 z31c25 = false := by decide +kernel

private def z31c26 : State := [0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e26 : optimized 6 1 z31c26 = false := by decide +kernel

private def next : Layer := #[z31c0,z31c1,z31c2,z31c3,z31c4,z31c5,z31c6,z31c7,z31c8,z31c9,z31c10,z31c11,z31c12,z31c13,z31c14,z31c15,z31c16,z31c17,z31c18,z31c19,z31c20,z31c21,z31c22,z31c23,z31c24,z31c25,z31c26]
private theorem afterStep : AtlasCut.Anchors 6 next := by
  intro s mem nd
  simp only [next, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AtlasCut.leaf e0 nd
  · exact AtlasCut.leaf e1 nd
  · exact AtlasCut.leaf e2 nd
  · exact AtlasCut.leaf e3 nd
  · exact AtlasCut.leaf e4 nd
  · exact AtlasCut.leaf e5 nd
  · exact AtlasCut.leaf e6 nd
  · exact AtlasCut.leaf e7 nd
  · exact AtlasCut.leaf e8 nd
  · exact AtlasCut.leaf e9 nd
  · exact AtlasCut.leaf e10 nd
  · exact AtlasCut.leaf e11 nd
  · exact AtlasCut.leaf e12 nd
  · exact AtlasCut.leaf e13 nd
  · exact AtlasCut.leaf e14 nd
  · exact AtlasCut.leaf e15 nd
  · exact AtlasCut.leaf e16 nd
  · exact AtlasCut.leaf e17 nd
  · exact AtlasCut.leaf e18 nd
  · exact AtlasCut.leaf e19 nd
  · exact AtlasCut.leaf e20 nd
  · exact AtlasCut.leaf e21 nd
  · exact AtlasCut.leaf e22 nd
  · exact AtlasCut.leaf e23 nd
  · exact AtlasCut.leaf e24 nd
  · exact AtlasCut.leaf e25 nd
  · exact AtlasCut.leaf e26 nd
private theorem completeStep : (#[s31] : Layer).all (stateOK next 7) = true := by decide +kernel
theorem node31 : s31.Nodup → ¬ live basicOps goal 7 s31.toFinset :=
  (AtlasCut.step afterStep completeStep) s31 (by simp)

end CutWords1150
