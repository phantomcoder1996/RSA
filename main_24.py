import random
import sys
import time
import timeit
import math
from matplotlib import pyplot as plt
from fractions import gcd





def convert_to_string(num):

    s = ""
    while num>0:

        char = chr(num&(0xFF))
        s = s+char
        num = num >> 8
    return s[::-1]





class MathUtils(object):
    def __init__(self):
        self.zzzz=""

    #Iterative implementation
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

    #Recursive implementation
    def extended_euclidean(self,a,b):
        if a == 0 :
            return b,0,1
        gcd,x1,y1 = self.extended_euclidean(b%a,a)
        x = y1 - (b//a)*x1
        y = x1
        return gcd,x,y

    def generate_random_number(self,bl):
        x = random.getrandbits(bl)
        x |= (1<<(bl-1)) | 1
        return x



class prime_generator(object):


    # miller rabin test
    def miller_test(self,n,r):

        a = random.randint(2,n-2)
        x = pow(a,r,n)


        if x == 1 or x == n-1:
            return True
        while r != n-1:

            break
            r = r << 1
            x = (x * x) % n
            if x == 1 :
                return False
            if x == n-1:
                return True
        return False




    def is_prime(self,n,k=128):
        if n == 2 or n == 3 :
            return True
        if n<=1 or n&1 == 0 :
            return False
        else:

            r = n - 1 #even initially
            # get r and s such that n-1 = r * 2^s and r is odd

            s = 0
            while r&1 != 1: # r is not add
                s = s+1
                r  = r >> 1

        # based on desired accuracy (perform test k times)
            for i in range(k):

                if (self.miller_test(n,r)== False): #n is composite
                    return False

            return True #n is probably prime



    def generate_large_prime(self,bit_length):

        x = random.getrandbits(bit_length)
        x |= (1 << (bit_length-1))| 1

        while not self.is_prime(x,128):
            x = random.getrandbits(bit_length)
            x |= (1<< (bit_length-1))| 1
        return x











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
        self.mu = MathUtils()







    def generate_relatively_prime_number(self,n):

        m_gcd = 0
        cnt = 0

        while m_gcd != 1:
            e = random.randint(3,n-1) #start from 5 because less than that the public key will be very small
            m_gcd,d,_ = self.mu.extended_euclidean(e,n)
            cnt = cnt + 1



        while d < 0:
            d = d + n
        d = d%n

        return e,d

    def generate_relatively_prime_number_of_length(self,n,bl):

            m_gcd = 0
            cnt = 0
            MU = MathUtils()

            while m_gcd != 1:
                e = MU.generate_random_number(bl)
                m_gcd,d,_ = self.mu.extended_euclidean(e,n)
                cnt = cnt + 1



            while d < 0:
                d = d + n
            d = d%n

            return e,d





class RSA(object):

    def __init__(self,m_prime_generator):
        self.prime_gen = m_prime_generator
        self.key_length = 1024

    def _modulo_fast_exponentiation_rec(self,a,b,n):
        if b == 1:
            return a
        if b == 0:
            return 1
        x = self._modulo_fast_exponentiation_rec(a,b//2,n)

        return (x*x)%n if b&1 == 0 else (x*x*a)%n


    def _modulo_fast_exponentiation(self,a,b,n): #a^b%n

        res = 1
        x = a
        while b>0:
            if b&1 == 1:
                res = (res * x)%n

            b = b >> 1
            x =( x * x )%n

        return res%n



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
        self.key_length = key_length
        l = key_length//2
        p = self.prime_gen.generate_large_prime(l)
        q = self.prime_gen.generate_large_prime(l)
        self.n = p*q

        while int.bit_length(self.n) !=key_length:
            p = self.prime_gen.generate_large_prime(l)
            q = self.prime_gen.generate_large_prime(l+1)
            self.n = p*q


        phi_n = (p-1)*(q-1)



        self.e,self.d = self.prime_gen.generate_relatively_prime_number(phi_n)



    def get_public_key(self):
        return self.n,self.e

    def get_private_key(self):
        return self.n,self.d




    def encrypt(self,m,e,n):
        #Assume the ascii string is a number in the base 256, so to get that number

        #first convert the string to number assume the first character to be the most significant

        block_size = max(self.key_length//2,8)

        num_blocks  = int(math.ceil((len(m)*8)/block_size))

        cnt = 0
        size = len(m)
        j =0
        cipher = []
        while cnt < num_blocks:
            number = 0

            minimum_sz = min(size,block_size//8)

            for i in range(j,j+minimum_sz):
                number = number | int(ord(m[i]))
                if i<j+minimum_sz-1:
                    number = number << 8
            size = size-minimum_sz

            j = j + minimum_sz
            cnt +=1
            c = self._modulo_fast_exponentiation(number,e,n)
            cipher.append(c)




        return cipher

    def decrypt(self,c,d,n):
        numbers = []

        for chr in c:
            num = self._modulo_fast_exponentiation(chr,d,n)
            numbers.append(num)


        return numbers







class Receiver(object):


    def __init__(self,name,RSA):
        self.name = name
        self.rsa = RSA

    def generate_key(self):

        print("%s generates public and private keys"%(self.name))
        self.rsa.generate_assymetric_key(key_length=1024)
        return self.rsa.get_public_key()


    def receive(self,c):

        n,d = self.rsa.get_private_key()
        print("%s decrypts the message using her private key(%d,%d)"%(self.name,n,d))
        numbers = self.rsa.decrypt(c,d,n)

        restored_message = ""
        for number in numbers:
            restored_message = restored_message + convert_to_string(number)

        print("%s has restored the message: %s"%(self.name,restored_message))


class Sender(object):
    def __init__(self,name,rsa):
        self.name = name
        self.rsa = rsa

    def send(self,m,n,e):
        print("%s has the message: %s"%(self.name,m))

        c = self.rsa.encrypt(m,e,n)
        print("Bob encrypts the message m and generates the cipher %s"%c)
        return c







def RSA_simulation(message):
    pg = prime_generator()
    m_RSA = RSA(pg)

    Alice = Receiver("Alice",m_RSA)
    n,e = Alice.generate_key()
    Bob = Sender("Bob",m_RSA)
    c=Bob.send(message,n,e)
    Alice.receive(c)


def RSA_efficiency_test():
    print()
    #Test the effect of n on RSA time
    key_lengths = [int(pow(2,i)) for i in range(4,11)]
    timing = []
    m = "h"

    pg=prime_generator()
    m_RSA =RSA(pg)
    for kl in key_lengths:

        m_RSA.generate_assymetric_key(key_length=kl)
        n,e = m_RSA.get_public_key()
        print("n=%d , length in bits=%d "%(n,int.bit_length(n)))

        start = time.time()
        _ = m_RSA.encrypt(m,e,n)
        end = time.time()
        timing.append(end-start)


    plt.plot(key_lengths,timing)
    plt.xlabel("key_length (bits)")
    plt.ylabel("time (sec)")
    plt.xticks(key_lengths)
    plt.title("Effect of key length on efficiency of encryption")
    plt.show()


    # Testing the effect of changing e and keeping n constant

    key_lengths = [int(pow(2,i)) for i in range(3,10)]
    timing=[]
    pg = prime_generator()
    p = pg.generate_large_prime(512)
    q = pg.generate_large_prime(512)
    n = p*q
    phi_n = (p-1)*(q-1)
    for kl in key_lengths:
        e,_ = pg.generate_relatively_prime_number_of_length(phi_n,kl)
        print("e=%d"%e)
        start = time.time()
        _ = m_RSA.encrypt(m,e,n)
        end = time.time()
        timing.append(end-start)
    plt.plot(key_lengths,timing)
    plt.xlabel("key_length (bits)")
    plt.ylabel("time (sec)")
    plt.xticks(key_lengths)
    plt.title("Effect of length of e on efficiency of encryption at constant n")
    plt.show()








class Attack(object):
    def __init__(self):
        self.key_lengths = [int(pow(2,i)) for i in range(2,7)]
        self.timing = []
        #self.m = 390
        pg = prime_generator()
        self.m_RSA = RSA(pg)


        # Brute force attack
        print()
        print("Brute force attack")
        self.get_private_key()
        # Chosen cipher text attack
        print()
        print("Chosen cipher text attack")
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
        p = int(float((primes[0])))
        q = int(float((n / p)))

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




            gcd,d,_ = MU.extended_euclidean(e,phin)

            while d<0:
                d = d+ phin

            d = d%phin

            end = time.time()

            print("original vs extracted %d %d"%(dpr,d))
            self.timing.append(end - start)
        plt.plot(self.key_lengths, self.timing)
        plt.xlabel("key_length (bits)")
        plt.ylabel("time(sec)")
        plt.xticks( self.key_lengths)
        plt.title("Time to get Private Key.")
        plt.show()







    def choosen_cipher_text_attack(self):

        self.m_RSA.generate_assymetric_key(key_length = 1024)
        n, e = self.m_RSA.get_public_key()
        m = "Error 404 => Brain lost in project"

        C = self.m_RSA.encrypt(m, e, n)

        #Multiply the cypher text by 2^e %n
        C_a = pow(2, e, n)
        C_b = [c * C_a for c in C]

        # Send the new cipher text to the victim to sign it with his private key
        _, dpr = self.m_RSA.get_private_key()
        C_b_d = self.m_RSA.decrypt(C_b, dpr, n)



        # Restore the message again
        MU = MathUtils()
        two_inverse = MU.modinv(2, n)

        restored_message_number = [(C_b* two_inverse) % n for C_b in C_b_d]
        original_msg = [convert_to_string(cb) for cb in restored_message_number]
        restored_message=""
        for msg_block in original_msg:
            restored_message = restored_message  + msg_block
        print ('Restored Message: %s VS Original Message: %s'%(restored_message,m))
        # get C_b_d
        # ciper sent = (2M)^e mod n
        # C_b_d = (C_b)^d mod n = (2M) mod n












if __name__ == '__main__':

    #1 - RSA Simulation
    RSA_simulation("Security project Spring 2019")
    #2 - Encryption efficiency
    RSA_efficiency_test()
    #3 - Brute force attack &&  #4 - Chosen cipher text attack
    attack = Attack()





















