import json
import tkinter as tk
from tkinter import scrolledtext, messagebox
import socket
import threading
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
import secrets

from HFE import self


class HFE:

    def __init__(self, n=128, mod_poly=None, generate_keys=True):
        self.n = n
        self.n_bytes = (n + 7) // 8
        if mod_poly is None:
            if n == 8:
                mod_poly = 0x11B
            elif n == 16:
                mod_poly = 0x144CB
            elif n == 128:
                mod_poly = (1 << 128) ^ (1 << 7) ^ (1 << 2) ^ (1 << 1) ^ 1
            else:
                mod_poly = self._find_irreducible(n)
        self.mod_poly = mod_poly
        self.S_matrix = self._random_invertible_matrix(n)
        self.S_vector = secrets.randbits(n)
        self.T_matrix = self._random_invertible_matrix(n)
        self.T_vector = secrets.randbits(n)

        self.S_inv_matrix = self._invert_matrix(self.S_matrix)
        self.T_inv_matrix = self._invert_matrix(self.T_matrix)
        self.S_inv_vector = self._matrix_vector_mult(self.S_inv_matrix, self.S_vector)
        self.T_inv_vector = self._matrix_vector_mult(self.T_inv_matrix, self.T_vector)

        order = (1 << n) - 1
        while True:
            e = secrets.randbits(n) % order
            if e <= 1:
                continue
            if e & (e - 1) == 0:
                continue

            def gcd(a, b):
                while b:
                    a, b = b, a % b
                return a

            if gcd(e, order) == 1:
                self.e = e
                break

        def egcd(a, b):
            if a == 0:
                return (b, 0, 1)
            g, y, x = egcd(b % a, a)
            return (g, x - (b // a) * y, y)

        _, x, _ = egcd(self.e, order)
        self.e_inv = x % order
        self.c = secrets.randbits(n)

        if self.n_bytes not in (16, 24, 32):
            raise ValueError(
                f"Недопустимый размер поля GF(2^{n}) для шифрования: ключ {self.n_bytes} байт не поддерживается AES.")

    @classmethod
    def from_public_parameters(cls, params):
        hfe = cls(
            n=params['n'],
            mod_poly=params['mod_poly'],
            generate_keys=False)

        hfe.S_matrix = params['S_matrix']
        hfe.S_vector = params['S_vector']
        hfe.T_matrix = params['T_matrix']
        hfe.T_vector = params['T_vector']
        hfe.e = params['e']
        hfe.c = params['c']

        hfe.S_inv_matrix = hfe._invert_matrix(hfe.S_matrix)
        hfe.T_inv_matrix = hfe._invert_matrix(hfe.T_matrix)
        hfe.S_inv_vector = hfe._matrix_vector_mult(hfe.S_inv_matrix, hfe.S_vector)
        hfe.T_inv_vector = hfe._matrix_vector_mult(hfe.T_inv_matrix, hfe.T_vector)

        order = (1 << hfe.n) - 1

        def egcd(a, b):
            if a == 0: return (b, 0, 1)
            g, y, x = egcd(b % a, a)
            return (g, x - (b // a) * y, y)

        _, x, _ = egcd(hfe.e, order)
        hfe.e_inv = x % order

        return hfe

    def encrypt(self, plaintext: bytes) -> bytes:

        if isinstance(plaintext, str):
            plaintext = plaintext.encode('utf-8')
        sym_key = secrets.token_bytes(self.n_bytes)

        key_int = int.from_bytes(sym_key, 'big')
        enc_key_int = self._encrypt_int(key_int)
        enc_key_bytes = enc_key_int.to_bytes(self.n_bytes, 'big')

        aesgcm = AESGCM(sym_key)
        nonce = secrets.token_bytes(12)
        ciphertext = aesgcm.encrypt(nonce, plaintext, None)

        return enc_key_bytes + nonce + ciphertext

    def decrypt(self, ciphertext: bytes) -> bytes:

        if len(ciphertext) < self.n_bytes + 12:
            raise ValueError("Некорректный шифротекст или несоответствие параметров.")
        enc_key_bytes = ciphertext[:self.n_bytes]
        nonce = ciphertext[self.n_bytes:self.n_bytes + 12]
        enc_data = ciphertext[self.n_bytes + 12:]

        enc_key_int = int.from_bytes(enc_key_bytes, 'big')
        sym_key_int = self._decrypt_int(enc_key_int)
        sym_key = sym_key_int.to_bytes(self.n_bytes, 'big')

        aesgcm = AESGCM(sym_key)
        try:
            plaintext = aesgcm.decrypt(nonce, enc_data, None)
        except Exception:
            raise ValueError("Не удалось расшифровать: данные повреждены или ключ неверен.")
        return plaintext

    def _encrypt_int(self, x: int) -> int:
        x_vec = self._int_to_bits(x, self.n)
        u_vec = self._matrix_vector_mult(self.S_matrix, x_vec) ^ self.S_vector

        u = self._bits_to_int(u_vec, self.n)
        w = self._gf_pow(u, self.e) ^ self.c

        w_vec = self._int_to_bits(w, self.n)
        y_vec = self._matrix_vector_mult(self.T_matrix, w_vec) ^ self.T_vector
        return self._bits_to_int(y_vec, self.n)

    def _decrypt_int(self, y: int) -> int:

        y_vec = self._int_to_bits(y, self.n)
        w_vec = self._matrix_vector_mult(self.T_inv_matrix, y_vec ^ self.T_vector)

        w = self._bits_to_int(w_vec, self.n)
        rhs = w ^ self.c

        u = 0 if rhs == 0 else self._gf_pow(rhs, self.e_inv)
        u_vec = self._int_to_bits(u, self.n)

        x_vec = self._matrix_vector_mult(self.S_inv_matrix, u_vec ^ self.S_vector)
        return self._bits_to_int(x_vec, self.n)

    def _random_invertible_matrix(self, n: int) -> list[int]:

        while True:
            matrix = [secrets.randbits(n) for _ in range(n)]
            try:
                self._invert_matrix(matrix)
                return matrix
            except ValueError:
                continue

    def _invert_matrix(self, matrix: list[int]) -> list[int]:
        n = len(matrix)
        M = matrix.copy()
        I = [1 << i for i in range(n)]
        for i in range(n):
            if not (M[i] >> i) & 1:
                swap_row = i + 1
                while swap_row < n and not (M[swap_row] >> i) & 1:
                    swap_row += 1
                if swap_row == n:
                    raise ValueError("Матрица вырожденная")
                M[i], M[swap_row] = M[swap_row], M[i]
                I[i], I[swap_row] = I[swap_row], I[i]
            for j in range(n):
                if j != i and ((M[j] >> i) & 1):
                    M[j] ^= M[i]
                    I[j] ^= I[
                        i]
        return I

    def get_public_parameters(self):
        return {
            'n': self.n,
            'mod_poly': self.mod_poly,
            'S_matrix': self.S_matrix,
            'S_vector': self.S_vector,
            'T_matrix': self.T_matrix,
            'T_vector': self.T_vector,
            'e': self.e,
            'c': self.c,
        }

    def _matrix_vector_mult(self, matrix: list[int], vector: int) -> int:

        result = 0
        for i, row in enumerate(matrix):
            if (row & vector).bit_count() % 2:
                result |= (1 << i)
        return result

    def _gf_multiply(self, a: int, b: int) -> int:
        res = 0
        while a:
            if a & 1:
                res ^= b
            a >>= 1
            b <<= 1
            if b & (1 << self.n):
                b ^= self.mod_poly
        return res

    def _gf_pow(self, base: int, exp: int) -> int:
        result = 1
        x = base
        e = exp
        while e > 0:
            if e & 1:
                result = self._gf_multiply(result, x)
            x = self._gf_multiply(x, x)
            e >>= 1
        return result

    def _int_to_bits(self, x: int, n_bits: int) -> int:
        return x & ((1 << n_bits) - 1)

    def _bits_to_int(self, bits: int, n_bits: int) -> int:
        return bits & ((1 << n_bits) - 1)

    def _find_irreducible(self, n: int) -> int:
        while True:
            poly = (1 << n) | 1 | (secrets.randbits(n - 1) << 1)
            if self._is_irreducible(poly, n):
                return poly

    @staticmethod
    def _is_irreducible(poly: int, n: int) -> bool:
        if poly & 1 == 0:
            return False
        X = 2

        def mod_mul(a: int, b: int) -> int:
            res = 0
            while a:
                if a & 1:
                    res ^= b
                a >>= 1
                b <<= 1
                if b & (1 << n):
                    b ^= poly
            return res

        for d in range(1, n):
            if n % d == 0:
                r = X
                for _ in range(d):
                    r = mod_mul(r, r)
                if r == X:
                    return False
        return True




class SecureChatClient:
    def __init__(self, host, port):
        self.host = host
        self.port = port
        self.hfe = HFE()
        self.peer_public_keys = {}
        self.setup_gui()
        self.setup_network()
        self.start_listening()

    def setup_gui(self):
        self.root = tk.Tk()
        self.root.title(f"Защищенный HFE чат - {self.host}:{self.port}")

        self.message_entry = tk.Entry(self.root, width=50)
        self.message_entry.pack(pady=5)

        recipient_frame = tk.Frame(self.root)
        recipient_frame.pack(pady=5)

        self.ip_entry = tk.Entry(recipient_frame, width=20)
        self.ip_entry.pack(side=tk.LEFT, padx=2)
        self.ip_entry.insert(0, "127.0.0.1")

        self.port_entry = tk.Entry(recipient_frame, width=7)
        self.port_entry.pack(side=tk.LEFT, padx=2)
        self.port_entry.insert(0, "")

        tk.Button(self.root, text="Отправить", command=self.send_message).pack(pady=5)

        self.message_area = scrolledtext.ScrolledText(self.root, width=60, height=20)
        self.message_area.pack(padx=10, pady=10)

    def setup_network(self):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.bind((self.host, self.port))
        self.sock.listen(5)

    def start_listening(self):
        self.listener = threading.Thread(target=self.receive_connections, daemon=True)
        self.listener.start()

    def receive_connections(self):
        while True:
            client, addr = self.sock.accept()
            threading.Thread(target=self.handle_client, args=(client, addr)).start()

    def handle_client(self, client, addr):
        try:
            data = client.recv(4096 * 10)
            if not data:
                return
            peer_public = self.deserialize_public_key(data)
            self.peer_public_keys[addr] = peer_public

            my_public = self.serialize_public_key(self.hfe.get_public_parameters())
            client.sendall(my_public)

            encrypted = client.recv(4096)
            if encrypted:
                decrypted = self.hfe.decrypt(encrypted)
                self.display_message(f"[{addr[0]}:{addr[1]}] {decrypted.decode('utf-8')}")
        except Exception as e:
            self.display_message(f"[Error] Ошибка обработки сообщения: {str(e)}")
        finally:
            client.close()

    def send_message(self):
        message = self.message_entry.get()
        if not message:
            return

        recipient_ip = self.ip_entry.get()
        recipient_port = int(self.port_entry.get())
        recipient_address = (recipient_ip, recipient_port)

        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(recipient_address)

                public_params = self.hfe.get_public_parameters()
                serialized_public = self.serialize_public_key(public_params)
                s.sendall(serialized_public)

                received_data = s.recv(4096 * 10)
                if not received_data:
                    raise ValueError("Не получен публичный ключ от получателя.")
                peer_public = self.deserialize_public_key(received_data)
                self.peer_public_keys[recipient_address] = peer_public

                hfe_peer = self.hfe.from_public_parameters(peer_public)
                encrypted = hfe_peer.encrypt(message.encode())

                s.sendall(encrypted)

                self.display_message(f"[Вы → {recipient_ip}:{recipient_port}] {message}")
                self.message_entry.delete(0, tk.END)
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def serialize_public_key(self, public_params):
        data = {
            'n': public_params['n'],
            'mod_poly': hex(public_params['mod_poly']),
            'S_matrix': [hex(x) for x in public_params['S_matrix']],
            'S_vector': hex(public_params['S_vector']),
            'T_matrix': [hex(x) for x in public_params['T_matrix']],
            'T_vector': hex(public_params['T_vector']),
            'e': hex(public_params['e']),
            'c': hex(public_params['c']),
        }
        return json.dumps(data).encode('utf-8')

    def deserialize_public_key(self, data):
        data_str = data.decode('utf-8')
        obj = json.loads(data_str)
        return {
            'n': obj['n'],
            'mod_poly': int(obj['mod_poly'], 16),
            'S_matrix': [int(x, 16) for x in obj['S_matrix']],
            'S_vector': int(obj['S_vector'], 16),
            'T_matrix': [int(x, 16) for x in obj['T_matrix']],
            'T_vector': int(obj['T_vector'], 16),
            'e': int(obj['e'], 16),
            'c': int(obj['c'], 16),
        }

    def display_message(self, text):
        self.message_area.insert(tk.END, text + "\n")
        self.message_area.see(tk.END)
        self.root.update()

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Использование: python secure_chat.py [PORT]")
        sys.exit(1)
    try:
        port = int(sys.argv[1])
        app = SecureChatClient('localhost', port)
        app.run()
    except ValueError:
        print("Порт должен быть числом")
        sys.exit(1)
