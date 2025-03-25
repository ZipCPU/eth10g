#include "board.h"
#include "txfns.h"

int main(int argc, char **argv) {
	const int	NLANES = 8;

	for(int k=0; k<NLANES; k++) {
		unsigned *lanep = (unsigned *)_ddr3_phy;
		lanep += k*32;

		txstr("PHY Lane: "); txdecimal(k); txstr("\n");
		txstr("  0. ODELAY-DATA,COUNT-IN: 0x"); txhex(lanep[0]); txstr("\n");
		txstr("  1. ODELAY-DQS ,COUNT-IN: 0x"); txhex(lanep[1]); txstr("\n");
		txstr("  2. IDELAY-DATA,COUNT-IN: 0x"); txhex(lanep[2]); txstr("\n");
		txstr("  3. IDELAY-DQS ,COUNT-IN: 0x"); txhex(lanep[3]); txstr("\n");
		txstr("  4. V[4]                : 0x"); txhex(lanep[4]); txstr("\n");
		txstr("  5. ADDED-READ-PIPE     : 0x"); txhex(lanep[5]); txstr("\n");
		if (1 == k) {
		txstr("  15.CORRECT-READ-DATA   : 0x"); txhex(lanep[15]); txstr("\n");
		txstr("  16.WRONG-READ-DATA     : 0x"); txhex(lanep[16]); txstr("\n");
		txstr("  18.CHECK-WORD (== 0x50): 0x"); txhex(lanep[18]); txstr("\n");
		}
	}
}
