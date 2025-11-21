# Security Bits
This file describes how we compute security bits for various challenges in our proof system.  
In order to guarantee a certain level of security (e.g., 100 bits), we use PoW before drawing random challenges in our protocol (this method is described here: https://eprint.iacr.org/2021/582.pdf).

## Security bits for single proof
Here's the full list of challenges that we need to draw in the single proof:
* lookup challenges (linearization challenges and gamma challenge)
* quotient alpha challenge
* quotient z challenge
* deep poly alpha challenge
* FRI folding challenges
* FRI queries challenges

To determine how many PoW bits are needed before drawing each challenge, we need to calculate number of security bits for each challenge.
Then `pow_bits_for_challenge = target_security_bits - security_bits_for_challenge`.

### Lookup security bits
We use cq lookup argument: https://eprint.iacr.org/2022/1763.pdf
The error bound is described here: https://eprint.iacr.org/2022/1530.pdf:
$$e \leq \frac{(M+1)\cdot|H| - 1}{|F| - |H|} + \frac{K + 1}{|F|}$$
Where $M$ is the number of lookup constraints, $K \leq M$ (see definition in the paper), $|H|$ is the size of the initial domain and $|F|$ is the size of the field.  
We can bound $|F| - |H|$ as $\frac{|F|}{2}$ then:
$$e \leq \frac{(M+1)\cdot|H| + K}{|F| - |H|} \leq 2\frac{(M+2)\cdot|H|}{|F|}$$
$M+2$ is still something small, so we can bound it with 16 for our system, then:
$$security\_bits = -log_2(e) = -log_2(2) - log_2(16) - log_2(|H|) + log_2(|F|) = - 5 - log_2(|H|) + log_2(|F|)$$

### Quotient alpha security bits
We can use error bound from https://eprint.iacr.org/2022/1216.pdf: $e \leq L^{+} \cdot \frac{C}{|F|}$.  
Where $C$ is the number of constraints, $|F|$ - the size of the field, $H$ - initial domain, $D$ - sampling domain, $m \geq 3$ - constant and 
$$L^{+} = \frac{m + \frac{1}{2}}{\sqrt{\frac{|H|+2}{|D|}}}.$$
We can bound $\frac{|H|+2}{|D|}$ by $\frac{|H|}{|D|} = \frac{1}{lde\_factor}$, and set $m=3.5$, then:
$$e \leq 4\sqrt{lde\_factor} \cdot \frac{C}{|F|}$$
Then secutity bits can be computed as:
$$security\_bits = -log_2(e) = -log_2(4) - \frac{1}{2}log_2(lde\_factor) - log_2(C) + log_2(|F|)$$

### Quotient z security bits
We can use error bound from https://eprint.iacr.org/2022/1216.pdf: 
$$e \leq L^{+} \cdot \frac{d(|H|+1) + (|H|-1)}{|F| - |H \cup D|}$$
Where $d$ is the maximum constraint degree and the rest are the same. We can bound $|F| - |H \cup D|$ as $\frac{|F|}{2}$, $d(|H|+1) + (|H|-1)$ as $2d|H|$ and $L^{+}$ as previousely then:
$$security\_bits = -log_2(e) = -log_2(4) - \frac{1}{2}log_2(lde\_factor) - 1 - log_2(d) - log_2(|H|) + log_2(|F|) - 1$$
As far as $d$ = 2 for us, and $\frac{1}{2}log_2(lde\_factor) + log_2(|H|) /leq log_2(|D|)$, we can simplify it to:
$$security\_bits = -log_2(e) = -log_2(|D|) + log_2(|F|) - 5$$

### Deep poly alpha security bits
Here we use bound from: https://hackmd.io/@pgaf/HkKs_1ytT#fnref2: $e \leq \frac{|D|\cdot t}{|F|}$, where $t$ is the number of batched polynomials.
Then:
$$security\_bits = -log_2(e) = -log_2(t) - log_2(|D|) + log_2(|F|)$$

### FRI folding challenges security bits
Here for each folding round we compute separately. We use similar bound from https://hackmd.io/@pgaf/HkKs_1ytT#fnref2:
$$e \leq \frac{(|D|+1)(l_i - 1)}{|F|}$$
Where $l_i$ is the folding factor at round $i$. We can bound $(|D|+1)(l_i - 1)$ as $|D| \cdot l_i$ then:
$$security\_bits = -log_2(e) = -log_2(l_i) - log_2(|D|) + log_2(|F|)$$

### FRI queries challenges security bits
We use bound from https://eprint.iacr.org/2025/2010.pdf: $e \leq (\frac{1}{lde\_factor})^{k}$, where $k$ is the number of queries. Then:
$$security\_bits = -log_2(e) = k \cdot log_2(lde\_factor)$$
PS due to the newer knowledge it’s less (~80% from the above value) 

## Security bits for whole layer
We also have some arguments that are shared between multiple proofs in the proofs layer:
* memory argument
* delegation argument
* state permutation

### Memory argument and state permutation security bits
Our memory argument is based on https://eprint.iacr.org/2023/1115.pdf. So what we actually want to prove is permutation of rows.
The error bound for permutation argument is: $e \leq \frac{n}{|F|}$, where $n$ is the number of rows in the permutation (in our case it's the number of cycles $N_{cycles}$ times the number of memory accesses per cycle $4$).  
Then the security bits can be computed as:
$$security\_bits = -log_2(e) = - 2 - log_2(N_{cycles}) + log_2(|F|)$$

### Delegation argument security bits
Here we use the same lookup structure as in the single proof, but instead of initial domain size $|H|$ we use the total number of cycles in all proofs: $N_{cycles}$.  
Then the security bits can be computed as:
$$security\_bits = - 5 - log_2(N_{cycles}) + log_2(|F|)$$
