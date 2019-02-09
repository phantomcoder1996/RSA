import random
import sys
import time
import timeit
import math
from matplotlib import pyplot as plt




def extended_euclidean(a,b):
        if a == 0 :
            return b,0,1
        gcd,x1,y1 = extended_euclidean(b%a,a)
        x = y1 - (b//a)*x1
        y = x1
        return gcd,x,y


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







    def generate_relatively_prime_number(self,n):

        m_gcd = 0
        cnt = 0

        while m_gcd != 1:
            e = random.randint(3,n-1) #start from 5 because less than that the public key will be very small
            m_gcd,d,_ = extended_euclidean(e,n)
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
        self.n = 0
        while len(str(self.n))!=key_length:
            large_primes = self.prime_gen.get_large_primes(lower_bound,upper_bound)

            p,q = self.generate_2_distinct_primes(large_primes)

            self.n = p*q
        phi_n = (p-1)*(q-1)

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
    m2 = m_RSA.decrypt(c,d,n)
    print("Alice restores the message m = %d"%m2)


def RSA_efficiency_test():
    #Test the effect of n on RSA time
    key_lengths = [i for i in range(4,14,2)]
    timing = []
    m = 390

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







if __name__ == '__main__':

    #1 - RSA Simulation
    RSA_simulation(201)
    #2 - Encryption efficiency
    RSA_efficiency_test()
    #3 - Brute force attack

    #4 - Chosen cipher text attack

















