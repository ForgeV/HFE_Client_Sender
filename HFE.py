import secrets
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# Создание объекта HFE с параметрами по умолчанию (поле GF(2^128))



class HFE:
    """
    Реализация схемы Hidden Field Equations (HFE) – асимметричного шифрования на основе скрытых многочленов.
    Поддерживает методы encrypt(plaintext) -> ciphertext и decrypt(ciphertext) -> plaintext.
    Использует гибридный подход: HFE-шифр применяется для шифрования симметричного ключа,
    а сами данные шифруются алгоритмом AES-GCM, что обеспечивает как конфиденциальность, так и целостность.
    """
    def __init__(self, n=128, mod_poly=None):
        """
        Инициализация объекта HFE и генерация ключей.
        :param n: Размер поля GF(2^n) в битах (по умолчанию 128 бит). Рекомендуется n >= 128 для высокой безопасности.
        :param mod_poly: Неприводимый полином степени n (целое число). Если не задан, выбирается стандартный или генерируется случайный.
        """
        self.n = n
        self.n_bytes = (n + 7) // 8  # число байт для представления элемента GF(2^n)
        # 1. Выбор неприводимого полинома для GF(2^n)
        if mod_poly is None:
            if n == 8:
                # Полином для GF(2^8): x^8 + x^4 + x^3 + x + 1 (0x11B)
                mod_poly = 0x11B
            elif n == 16:
                # Пример неприводимого полинома для GF(2^16): x^16 + x^14 + x^11 + x^10 + x^7 + x^6 + x^3 + x + 1
                mod_poly = 0x144CB
            elif n == 128:
                # Примитивный полином для GF(2^128) (из стандарта GCM): x^128 + x^7 + x^2 + x + 1
                mod_poly = (1 << 128) ^ (1 << 7) ^ (1 << 2) ^ (1 << 1) ^ 1
            else:
                # Генерация случайного неприводимого полинома степени n
                mod_poly = self._find_irreducible(n)
        self.mod_poly = mod_poly

        # 2. Генерация случайных обратимых матриц S и T (и соответствующих векторов сдвига) для аффинных преобразований
        self.S_matrix = self._random_invertible_matrix(n)
        self.S_vector = secrets.randbits(n)  # случайный вектор сдвига для S
        self.T_matrix = self._random_invertible_matrix(n)
        self.T_vector = secrets.randbits(n)  # случайный вектор сдвига для T

        # 3. Вычисление обратных матриц и векторов для S и T (для расшифрования)
        self.S_inv_matrix = self._invert_matrix(self.S_matrix)
        self.T_inv_matrix = self._invert_matrix(self.T_matrix)
        # Обратный вектор: S_inv_vector = S_inv_matrix * S_vector,  T_inv_vector = T_inv_matrix * T_vector
        self.S_inv_vector = self._matrix_vector_mult(self.S_inv_matrix, self.S_vector)
        self.T_inv_vector = self._matrix_vector_mult(self.T_inv_matrix, self.T_vector)

        # 4. Генерация центрального многочлена f(x) = x^e + c.
        # Выбираем случайную степень e, взаимно простую с 2^n - 1 (чтобы x^e было перестановкой множества ненулевых элементов поля),
        # и не равную степени 2 (чтобы избежать вырождения в линейное отображение).
        order = (1 << n) - 1  # порядок мультипликативной группы GF(2^n)
        while True:
            e = secrets.randbits(n) % order  # случайное 1 <= e < 2^n - 1
            if e <= 1:
                continue
            if e & (e - 1) == 0:  # e является степенью 2 (например, 2^k)?
                continue
            # Проверяем взаимную простоту e и 2^n-1
            def gcd(a, b):
                while b:
                    a, b = b, a % b
                return a
            if gcd(e, order) == 1:
                self.e = e
                break
        # Вычисляем обратную степень e_inv по модулю 2^n - 1 (для решения уравнения f(u) = w при расшифровании)
        def egcd(a, b):
            if a == 0:
                return (b, 0, 1)
            g, y, x = egcd(b % a, a)
            return (g, x - (b // a) * y, y)
        _, x, _ = egcd(self.e, order)
        self.e_inv = x % order

        # Свободный член c – случайный элемент поля GF(2^n)
        self.c = secrets.randbits(n)

        # 5. Проверка: длина симметричного ключа (n_bytes) должна соответствовать допустимым для AES (16, 24 или 32 байта)
        if self.n_bytes not in (16, 24, 32):
            raise ValueError(
                f"Недопустимый размер поля GF(2^{n}) для гибридного шифрования: ключ {self.n_bytes} байт не поддерживается AES.")

    def encrypt(self, plaintext: bytes) -> bytes:
        """
        Шифрует сообщение (байты) с помощью схемы HFE (гибридный режим).
        :param plaintext: открытый текст (bytes). Может быть также str (будет перекодирован в UTF-8).
        :return: шифротекст (bytes), содержащий зашифрованный ключ + nonce + зашифрованные данные.
        """
        if isinstance(plaintext, str):
            plaintext = plaintext.encode('utf-8')
        # 1. Генерируем случайный симметричный ключ (байтовой длины n_bytes)
        sym_key = secrets.token_bytes(self.n_bytes)
        # 2. Шифруем этот симметричный ключ с помощью схемы HFE (публичный ключ): y = P(x)
        key_int = int.from_bytes(sym_key, 'big')
        enc_key_int = self._encrypt_int(key_int)
        enc_key_bytes = enc_key_int.to_bytes(self.n_bytes, 'big')
        # 3. Шифруем данные алгоритмом AES-GCM на сгенерированном симметричном ключе
        aesgcm = AESGCM(sym_key)
        nonce = secrets.token_bytes(12)  # 96-битный случайный nonce
        ciphertext = aesgcm.encrypt(nonce, plaintext, None)
        # 4. Формируем итоговый шифротекст: [зашифрованный_ключ || nonce || ciphertext||tag]
        return enc_key_bytes + nonce + ciphertext

    def decrypt(self, ciphertext: bytes) -> bytes:
        """
        Расшифровывает сообщение с помощью схемы HFE (гибридный режим).
        :param ciphertext: шифротекст, полученный из encrypt() (bytes).
        :return: расшифрованный открытый текст (bytes).
        :raises ValueError: если данные повреждены или аутентификация не пройдена.
        """
        # 1. Разбираем формат шифротекста
        if len(ciphertext) < self.n_bytes + 12:
            raise ValueError("Некорректный шифротекст или несоответствие параметров.")
        enc_key_bytes = ciphertext[:self.n_bytes]  # зашифрованный симметричный ключ
        nonce = ciphertext[self.n_bytes:self.n_bytes + 12]  # 96-битный nonce AES-GCM
        enc_data = ciphertext[self.n_bytes + 12:]  # зашифрованные данные + тег аутентичности

        # 2. Расшифровываем симметричный ключ с помощью HFE (секретный ключ)
        enc_key_int = int.from_bytes(enc_key_bytes, 'big')
        sym_key_int = self._decrypt_int(enc_key_int)
        sym_key = sym_key_int.to_bytes(self.n_bytes, 'big')

        # 3. Расшифровываем данные алгоритмом AES-GCM
        aesgcm = AESGCM(sym_key)
        try:
            plaintext = aesgcm.decrypt(nonce, enc_data, None)
        except Exception:
            # Если произошла ошибка (например, тег аутентичности не сошёлся) – считаем шифртекст поврежденным
            raise ValueError("Не удалось расшифровать: данные повреждены или ключ неверен.")
        return plaintext

    # ================= Внутренние методы: реализация операций в GF(2^n) и генерация ключей =================

    def _encrypt_int(self, x: int) -> int:
        """Применяет публичное отображение P = T(f(S(x))) к элементу поля (целому x). Возвращает целое y."""
        # Аффинное преобразование S: u = S(x) = S_matrix * x_vec + S_vector
        x_vec = self._int_to_bits(x, self.n)
        u_vec = self._matrix_vector_mult(self.S_matrix, x_vec) ^ self.S_vector
        # Вычисляем значение центрального полинома: w = f(u) = u^e + c (в GF(2^n))
        u = self._bits_to_int(u_vec, self.n)
        w = self._gf_pow(u, self.e) ^ self.c
        # Преобразование T: y = T(w) = T_matrix * w_vec + T_vector
        w_vec = self._int_to_bits(w, self.n)
        y_vec = self._matrix_vector_mult(self.T_matrix, w_vec) ^ self.T_vector
        return self._bits_to_int(y_vec, self.n)


    def _decrypt_int(self, y: int) -> int:
        """Применяет приватное преобразование (T^{-1}, f^{-1}, S^{-1}) к элементу поля (целому y). Возвращает исходное x."""
        # Обратное преобразование T^{-1}: вычисляем w_vec, такой что w_vec = T_inv_matrix * (y_vec + T_vector)
        y_vec = self._int_to_bits(y, self.n)
        w_vec = self._matrix_vector_mult(self.T_inv_matrix, y_vec ^ self.T_vector)
        # Решаем уравнение f(u) = w. То есть находим u, что u^e + c = w.
        w = self._bits_to_int(w_vec, self.n)
        rhs = w ^ self.c  # правая часть уравнения u^e = w - c
        # Находим u как возведение rhs в степень e_inv (обратную к e) в GF(2^n)
        u = 0 if rhs == 0 else self._gf_pow(rhs, self.e_inv)
        u_vec = self._int_to_bits(u, self.n)
        # Обратное преобразование S^{-1}: x_vec = S_inv_matrix * (u_vec + S_vector)
        x_vec = self._matrix_vector_mult(self.S_inv_matrix, u_vec ^ self.S_vector)
        return self._bits_to_int(x_vec, self.n)

    def _random_invertible_matrix(self, n: int) -> list[int]:
        """Генерирует случайную невырожденную бинарную матрицу размера n x n (список целых, где каждый int представляет строку)."""
        while True:
            matrix = [secrets.randbits(n) for _ in range(n)]
            try:
                self._invert_matrix(matrix)
                return matrix  # если обратимая, возвращаем (self._invert_matrix не изменяет matrix существенно)
            except ValueError:
                continue  # повторяем попытку, если матрица вырожденная

    def _invert_matrix(self, matrix: list[int]) -> list[int]:
        """Вычисляет обратную матрицу над GF(2). Матрица задаётся списком целых (битовых строк). Возвращает список строк-целых для обратной матрицы."""
        n = len(matrix)
        # Копии исходной матрицы и единичной матрицы
        M = matrix.copy()
        I = [1 << i for i in range(n)]  # единичная матрица в битовом представлении (у i-й строки бит i = 1)
        for i in range(n):
            # Ищем строку с ненулевым элементом в i-м столбце на позиции не ниже i
            if not (M[i] >> i) & 1:
                swap_row = i + 1
                while swap_row < n and not (M[swap_row] >> i) & 1:
                    swap_row += 1
                if swap_row == n:
                    raise ValueError("Matrix is singular")  # матрица вырожденная (необратимая)
                # Меняем местами строки i и swap_row
                M[i], M[swap_row] = M[swap_row], M[i]
                I[i], I[swap_row] = I[swap_row], I[i]
            # Обнулияем i-й столбец во всех остальных строках
            for j in range(n):
                if j != i and ((M[j] >> i) & 1):
                    M[j] ^= M[i]   # XOR строк в матрице
                    I[j] ^= I[i]   # такой же XOR для единичной матрицы (накопление операций, превращающих её в обратную)
        # На выходе M должна преобразоваться в единичную матрицу, а I станет обратной матрицей
        return I

    def _matrix_vector_mult(self, matrix: list[int], vector: int) -> int:
        """Умножает матрицу (список битовых строк) на вектор (int) над GF(2). Возвращает результат в виде int (битового вектора)."""
        result = 0
        for i, row in enumerate(matrix):
            # Скалярное произведение строки на вектор по mod2: проверяем чётность единиц в (row & vector)
            if (row & vector).bit_count() % 2:
                result |= (1 << i)
        return result

    def _gf_multiply(self, a: int, b: int) -> int:
        """Перемножает два элемента GF(2^n), представленных целыми a и b. Редукция выполняется по модулю self.mod_poly."""
        res = 0
        # Алгоритм умножения в бинарном поле: двигаем `a` по битам `b` с редукцией
        while a:
            if a & 1:
                res ^= b  # добавляем b, если текущий бит a = 1
            a >>= 1
            b <<= 1
            # Если степень b достигла n (то есть бит n в 1), делаем редукцию по неприводимому полиному
            if b & (1 << self.n):
                b ^= self.mod_poly
        return res


    def _gf_pow(self, base: int, exp: int) -> int:
        """Возводит элемент GF(2^n) в степень exp методом бинарного возведения в степень."""
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
        """Представляет целое x как битовый вектор длины n_bits (возвращает int с соответствующими n_bits младшими битами)."""
        return x & ((1 << n_bits) - 1)

    def _bits_to_int(self, bits: int, n_bits: int) -> int:
        """Интерпретирует битовый вектор (int) как число (ограничивает число младшими n_bits битами)."""
        return bits & ((1 << n_bits) - 1)

    def _find_irreducible(self, n: int) -> int:
        """Генерирует случайный неприводимый полином степени n над GF(2). Возвращает его в виде целого числа."""
        # Случайный подбор полинома с проверкой неприводимости
        while True:
            # Формируем случайный полином степени n: старший и младший коэффициенты = 1 (чтобы степень была точно n и был ненулевой свободный член)
            poly = (1 << n) | 1 | (secrets.randbits(n-1) << 1)
            if self._is_irreducible(poly, n):
                return poly

    @staticmethod
    def _is_irreducible(poly: int, n: int) -> bool:
        """Проверяет, является ли бинарный полином (int) степени n неприводимым (критерий на основе равенства X^(2^d) mod f)."""
        if poly & 1 == 0:
            return False  # нет свободного члена -> делится на x
        X = 2  # полином X (в двоичном представлении 10)
        # Функция умножения полиномов по модулю poly (для проверки)
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
        # Проверяем условие: для всех собственных делителей d числа n должно выполняться X^(2^d) mod poly != X.
        for d in range(1, n):
            if n % d == 0:
                # Возводим X в степень 2^d (повторным возведением в квадрат d раз)
                r = X
                for _ in range(d):
                    r = mod_mul(r, r)
                if r == X:
                    return False  # poly делится на неприводимый полином степени d
        return True

hfe = HFE()
stringi = "gfjfjg"
# Шифрование сообщения
plaintext = b"Secret message"
ciphertext = hfe.encrypt(plaintext)
print("Ciphertext (hex):", ciphertext.hex())

# Расшифрование сообщения
decrypted = hfe.decrypt(ciphertext)
print("Decrypted:", decrypted)
# Проверка
print("Decryption successful?", decrypted == plaintext)
