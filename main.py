import random
import sys
import time
import timeit
import math
from matplotlib import pyplot as plt
from fractions import gcd




class prime_generator(object):



    def _sieve_prime_generator(self,n):

        test_prime = [True for _ in range(n) ]

        for i in range(2,n):
            if test_prime[i]:
                for j in range(2*i,n,i):

                    test_prime[j]=False

        self.primes = [i  for i in range(2,n) if test_prime[i]]


    def get_large_primes(self,lower_bound,upper_bound):
        large_primes = []
        i = 0
        end = len(self.primes)
        while i<end and self.primes[i]<upper_bound:
            if self.primes[i]>lower_bound:
                large_primes.append(self.primes[i])
            i = i + 1
        return large_primes


    def __init__(self):
        self.primes = []

        self._sieve_prime_generator(1000000)





    def extended_euclidean(self,a,b):
        if a == 0 :
            return b,0,1
        gcd,x1,y1 = self.extended_euclidean(b%a,a)
        x = y1 - (b//a)*x1
        y = x1
        return gcd,x,y


    def generate_relatively_prime_number(self,n):

        m_gcd = 0
        cnt = 0

        while m_gcd != 1:
            e = random.randint(5,n-1) #start from 5 because less than that the public key will be very small
            m_gcd,d,_ = self.extended_euclidean(e,n)
            cnt = cnt + 1


        while d < 0:
            d = d + n

        return e,d





class RSA(object):

    def __init__(self,m_prime_generator):
        self.prime_gen = m_prime_generator

    def _modulo_fast_exponentiation(self,a,b,n):
        if b == 1:
            return a
        if b == 0:
            return 1
        x = self._modulo_fast_exponentiation(a,b//2,n)

        return (x*x)%n if b&1 == 0 else (x*x*a)%n

    def _fast_exponentiation(self,a,b):
        if b == 1:
            return a
        if b == 0:
            return 1
        x = self._fast_exponentiation(a,b//2)

        return (x*x) if b&1 == 0 else (x*x*a)

    def generate_2_distinct_primes(self,large_primes):
        x = len(large_primes)//2
        i = random.randint(0,x)
        j = random.randint(x+1,len(large_primes)-1)
        return large_primes[i],large_primes[j]

    def generate_assymetric_key(self,key_length):
        l = key_length//2
        lower_bound = self._fast_exponentiation(10,l-1)
        upper_bound = self._fast_exponentiation(10,l)
        large_primes = self.prime_gen.get_large_primes(lower_bound,upper_bound)

        p,q = self.generate_2_distinct_primes(large_primes)

        self.n = p*q
        phi_n = (p-1)*(q-1)
        #print("phin , p, q",phi_n,p,q)

        self.e,self.d = self.prime_gen.generate_relatively_prime_number(phi_n)

    def get_public_key(self):
        return self.n,self.e

    def get_private_key(self):
        return self.n,self.d

    def encrypt(self,m,e,n):
        return self._modulo_fast_exponentiation(m,e,n)

    def decrypt(self,c,d,n):
        return self._modulo_fast_exponentiation(c,d,n)




def RSA_simulation(message):
    pg = prime_generator()
    m_RSA = RSA(pg)

    # Alice generates public and private keys
    print("Alice generates public and private keys")
    m_RSA.generate_assymetric_key(key_length=10)


    '''
    Bob has a message m to send to Alice
        1- Bob gets Alice's public key
        2- Bob encrypts the message
        3- Bob sends the message to Alice
     '''

    m = message
    print("Bob has the message %s"%m)
    n,e = m_RSA.get_public_key()
    print("Bob get's Alices public key (%d,%d)"%(n,e))
    c = m_RSA.encrypt(m,e,n)
    print("Bob encrypts the message m and generates the cipher %s"%c)

    '''
    Alice receives Bob's encrypted message c
        1- Alice uses her private key to decrypt the message
        2- Alice retrieves the message m
    
    '''
    print("Alice receives the cipher text %s"%c)
    n,d = m_RSA.get_private_key()
    print("Alice decrypts the message using her private key(%d,%d)"%(n,d))
    m = m_RSA.decrypt(c,d,n)
    print("Alice restores the message m = %d"%m)


def RSA_efficiency_test():
    #Test the effect of n on RSA time
    key_lengths = [i for i in range(4,14,2)]
    timing = []
    m = 39020

    # #use a constant e = 17 with different lengths of n
    # e = 17

    pg=prime_generator()
    m_RSA =RSA(pg)
    for kl in key_lengths:

        m_RSA.generate_assymetric_key(key_length=kl)
        n,e = m_RSA.get_public_key()
        print("n=%d"%n)
        start = time.time()
        _ = m_RSA.encrypt(m,e,n)
        end = time.time()
        timing.append(end-start)


    plt.plot(key_lengths,timing)
    plt.xlabel("key_length")
    plt.ylabel("time(sec)")
    plt.xticks([i for i in range(4,14,2)])
    plt.title("Effect of key length on efficiency of encryption")
    plt.show()


class MathUtils():
    def __init__(self):
        self.zzzz=""

    def extended_gcd(self,aa, bb):
        lastremainder, remainder = abs(aa), abs(bb)
        x, lastx, y, lasty = 0, 1, 1, 0
        while remainder:
            lastremainder, (quotient, remainder) = remainder, divmod(lastremainder, remainder)
            x, lastx = lastx - quotient * x, x
            y, lasty = lasty - quotient * y, y
        return lastremainder, lastx * (-1 if aa < 0 else 1), lasty * (-1 if bb < 0 else 1)

    def modinv(self,a, m):
        g, x, y = self.extended_gcd(a, m)
        if g != 1:
            raise ValueError
        return x % m



class Attack(object):
    def __init__(self):
        self.key_lengths = [i for i in range(4, 14, 2)]
        self.timing = []
        self.m = 39020
        pg = prime_generator()
        self.m_RSA = RSA(pg)
        self.get_private_key()
        self.choosen_cipher_text_attack()

    def getPrimes(self,n):


        c = int(math.sqrt(n))
        primes = []
        #print(c)
        if c%2==0:
            c = c+1
        for i in range(c,-1, -1):
            #print(i, n % i)
            if n % i == 0:
                primes.append(i)
                break
        p = primes[0]
        q = n / p
        phin = (p - 1) * (q - 1)

        return p, q, phin

    def get_private_key(self):
        MU = MathUtils()
        for kl in self.key_lengths:
            self.m_RSA.generate_assymetric_key(key_length=kl)
            n, e = self.m_RSA.get_public_key()
            _, dpr = self.m_RSA.get_private_key()
            start = time.time()
            p, q, phin = self.getPrimes(n)
            #print('Extracted phin ,p,q', phin, p, q)
            d = MU.modinv( e,phin)
            #print("Extraced Key VS Original Key", d, dpr)

            end = time.time()
            self.timing.append(end - start)
        plt.plot(self.key_lengths, self.timing)
        plt.xlabel("key_length")
        plt.ylabel("time(sec)")
        plt.xticks([i for i in range(4, 14, 2)])
        plt.title("Time to get Private Key.")
        plt.show()

    def get_message(self,c1, c2, e1, e2, N):
        if gcd(e1, e2) != 1:
            raise ValueError("e1 and e2 must be coprime")
        s1 = modinv(e1, e2)
        s2 = (gcd(e1, e2) - e1 * s1) / e2
        temp = modinv(c2, N)
        m1 = pow(c1, s1, N)
        m2 = pow(temp, -s2, N)
        return (m1 * m2) % N

    def choosen_cipher_text_attack(self):
        self.m_RSA.generate_assymetric_key(key_length = 10)
        n, e = self.m_RSA.get_public_key()
        m = 39020

        C = self.m_RSA.encrypt(m, e, n)
        C_a = pow(2, e, n)
        C_b = C * C_a
        _, dpr = self.m_RSA.get_private_key()
        C_b_d = self.m_RSA.decrypt(C_b, dpr, n)
        MU = MathUtils()
        two_inverse = MU.modinv(2, n)
        restored_message = (C_b_d* two_inverse) % n
        print ('Restored Message VS Original Message',restored_message,m)
        # get C_b_d
        # ciper sent = (2M)^e mod n
        # C_b_d = (C_b)^d mod n = (2M) mod n












if __name__ == '__main__':

    #1 - RSA Simulation
    RSA_simulation(201)
    #2 - Encryption efficiency
    RSA_efficiency_test()
    #3 - Brute force attack
    attack = Attack()



    #4 - Chosen cipher text attack

















