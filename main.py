import json
import tkinter as tk
from tkinter import scrolledtext, messagebox
import socket
import threading
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
import secrets

from HFE import hfe





class HFE:


        def __init__(self, n=128, mod_poly=None):
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

        def get_public_key(self) -> dict:
            """Возвращает публичные параметры, необходимые для шифрования."""
            return {
                "n": self.n,
                "mod_poly": self.mod_poly,
                "T_matrix": self.T_matrix,
                "T_vector": self.T_vector,
                "e": self.e,
                "c": self.c,
            }

        @classmethod
        def from_public_key(cls, public_key: dict):
            """Создает объект HFE только с публичным ключом (для шифрования)."""
            hfe = cls(n=public_key["n"], mod_poly=public_key["mod_poly"])
            hfe.T_matrix = public_key["T_matrix"]
            hfe.T_vector = public_key["T_vector"]
            hfe.e = public_key["e"]
            hfe.c = public_key["c"]
            return hfe

        def get_private_key(self) -> dict:
            """Возвращает все секретные параметры для расшифрования."""
            return {
                "n": self.n,
                "mod_poly": self.mod_poly,
                "S_matrix": self.S_matrix,
                "S_vector": self.S_vector,
                "S_inv_matrix": self.S_inv_matrix,
                "S_inv_vector": self.S_inv_vector,
                "T_inv_matrix": self.T_inv_matrix,
                "T_inv_vector": self.T_inv_vector,
                "e": self.e,
                "e_inv": self.e_inv,
                "c": self.c,
            }

        @classmethod
        def from_private_key(cls, private_key: dict):
            """Восстанавливает полный объект HFE из приватного ключа."""
            hfe = cls(n=private_key["n"], mod_poly=private_key["mod_poly"])
            hfe.S_matrix = private_key["S_matrix"]
            hfe.S_vector = private_key["S_vector"]
            hfe.S_inv_matrix = private_key["S_inv_matrix"]
            hfe.S_inv_vector = private_key["S_inv_vector"]
            hfe.T_inv_matrix = private_key["T_inv_matrix"]
            hfe.T_inv_vector = private_key["T_inv_vector"]
            hfe.e = private_key["e"]
            hfe.e_inv = private_key["e_inv"]
            hfe.c = private_key["c"]
            return hfe











class SecureChatClient:
    def __init__(self, host, port):
        self.host = host
        self.port = port
        self.hfe = HFE()  # Локальный ключевой пар
        self.public_keys = {}  # Хранилище чужих публичных ключей
        self.setup_gui()
        self.setup_network()
        self.start_listening()

    def setup_gui(self):
        self.root = tk.Tk()
        self.root.title(f"Защищенный HFE чат - {self.host}:{self.port}")

        # Кнопка для обмена ключами
        tk.Button(self.root, text="Обмен ключами", command=self.init_key_exchange).pack(pady=2)

        self.message_entry = tk.Entry(self.root, width=50)
        self.message_entry.pack(pady=5)

        recipient_frame = tk.Frame(self.root)
        recipient_frame.pack(pady=5)

        self.ip_entry = tk.Entry(recipient_frame, width=20)
        self.ip_entry.pack(side=tk.LEFT, padx=2)
        self.ip_entry.insert(0, "127.0.0.1")

        self.port_entry = tk.Entry(recipient_frame, width=7)
        self.port_entry.pack(side=tk.LEFT, padx=2)

        tk.Button(self.root, text="Отправить", command=self.send_message).pack(pady=5)

        self.message_area = scrolledtext.ScrolledText(self.root, width=60, height=20)
        self.message_area.pack(padx=10, pady=10)

    def setup_network(self):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.bind((self.host, self.port))
        self.sock.listen(5)

    def start_listening(self):
        self.listener = threading.Thread(target=self.receive_messages, daemon=True)
        self.listener.start()

    def init_key_exchange(self):
        """Инициировать обмен ключами с указанным получателем"""
        recipient = self.get_recipient_addr()
        self.request_public_key(recipient)

    def request_public_key(self, recipient):
        """Отправить запрос на получение публичного ключа"""
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(recipient)
                s.sendall(b'KEY_REQUEST:' + json.dumps({
                    'sender_ip': self.host,
                    'sender_port': self.port
                }).encode())
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось запросить ключ: {str(e)}")

    def handle_key_exchange(self, data, addr):
        """Обработка операций, связанных с обменом ключами"""
        if data.startswith(b'KEY_REQUEST:'):
            # Отправить наш публичный ключ запросившей стороне
            key_data = json.dumps(self.hfe.get_public_key()).encode()
            try:
                with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                    s.connect((addr[0], int(json.loads(data[12:])['sender_port'])))
                    s.sendall(b'KEY_RESPONSE:' + key_data)
            except Exception as e:
                self.display_message(f"[Ошибка] Не удалось отправить ключ: {str(e)}")

        elif data.startswith(b'KEY_RESPONSE:'):
            # Получить и сохранить публичный ключ
            try:
                key_data = json.loads(data[13:])
                recipient_addr = (key_data.get('sender_ip', addr[0]), key_data.get('sender_port', addr[1]))
                self.public_keys[recipient_addr] = hfe.from_public_key(key_data)
                self.display_message(f"[Система] Получен публичный ключ от {recipient_addr}")
            except Exception as e:
                self.display_message(f"[Ошибка] Некорректный ключ: {str(e)}")

    def get_recipient_addr(self):
        return (
            self.ip_entry.get(),
            int(self.port_entry.get())
        )

    def receive_messages(self):
        while True:
            try:
                client, addr = self.sock.accept()
                data = client.recv(4096)
                if data:
                    if data.startswith(b'KEY_'):
                        self.handle_key_exchange(data, addr)
                    else:
                        try:
                            decrypted = hfe.decrypt(data)
                            self.display_message(f"[{addr[0]}:{addr[1]}] {decrypted.decode('utf-8')}")
                        except Exception as e:
                            self.display_message(f"[Ошибка] Дешифровка: {str(e)}")
                client.close()
            except Exception as e:
                print(f"Ошибка приема: {e}")

    def send_message(self):
        message = self.message_entry.get()
        if not message:
            return

        try:
            recipient = self.get_recipient_addr()

            # Проверяем наличие публичного ключа получателя
            if recipient not in self.public_keys:
                self.request_public_key(recipient)
                raise ValueError("Публичный ключ получателя не найден. Запрошен...")

            # Шифруем сообщение публичным ключом получателя
            recipient_hfe = self.public_keys[recipient]
            encrypted = recipient_hfe.encrypt(message)

            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.connect(recipient)
                s.sendall(encrypted)

            self.display_message(f"[Я]: {message}")
            self.message_entry.delete(0, tk.END)
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))
    def display_message(self, text):
        self.message_area.insert(tk.END, text + "\n")
        self.message_area.see(tk.END)
        self.root.update()

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python secure_chat.py [PORT]")
        sys.exit(1)

    try:
        port = int(sys.argv[1])
        app = SecureChatClient('localhost', port)
        app.run()
    except ValueError:
        print("Invalid port number")
        sys.exit(1)
