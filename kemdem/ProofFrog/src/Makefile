all: test-parsing check-proof

test-parsing:
	python3 -m proof_frog parse SymEnc.primitive
	python3 -m proof_frog parse SymEnc-OTS.game
	python3 -m proof_frog parse KEM.primitive
	python3 -m proof_frog parse KEM-CPA.game
	python3 -m proof_frog parse PKE.primitive
	python3 -m proof_frog parse PKE-CPA.game
	python3 -m proof_frog parse Hyb.scheme
	python3 -m proof_frog parse Hyb-is-CPA.proof

check-proof:
	python3 -m proof_frog prove Hyb-is-CPA.proof