#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
======================================================================
 CALCULADORA DE MÉTODOS NUMÉRICOS
 Integración numérica y ecuaciones diferenciales (Euler y Runge-Kutta)
 Incluye Asistente Inteligente (Buscador / Recomendador de Métodos)
======================================================================

CÓMO USARLA

    No hay que instalar nada: usa solo la biblioteca estándar de Python
    (3.8 o superior) con Tkinter, que ya viene incluido en Windows y macOS.
    En Ubuntu/Debian:  sudo apt install python3-tk

QUÉ HACE
    1. Eliges un método en el menú de la izquierda (o usas el Asistente IA).
    2. Cambias los datos en los cuadros (función, límites, n, etc.).
    3. Presionas "Calcular" o la tecla Enter.
    4. Recibes el resultado, el paso a paso, la tabla de valores y una gráfica.
    Si algo no se puede resolver matemáticamente, el programa NO falla:
    explica la razón exacta (por ejemplo, "Simpson 1/3 necesita n par").

MÉTODOS INCLUIDOS (fórmulas de las Clases 5 y 6 del PDF)
    - Trapecio simple y compuesto            (ecuaciones 1, 2 y 8)
    - Simpson 1/3 simple y compuesto         (ecuaciones 3 y 9)
    - Simpson 3/8 simple y compuesto         (ecuaciones 4 y 10)
    - Newton-Cotes con n = 4, 5 y 6          (ecuaciones 5, 6 y 7)
    - Cuadratura Gaussiana, n = 2 a 10       (ecuaciones 11 a 21; Tabla 1 del PDF para n = 2, 3 y 4)
    - Euler                                  (Clase 6, ecuación 1)
    - Euler mejorado (Heun)                  (Clase 6, ecuación 2)
    - Runge-Kutta de orden 2, 3 y 4          (Clase 6, ecuaciones 3, 4 y 5)
      (más los órdenes 5 y 6 como extra: NO están en el PDF)

ASISTENTE INTELIGENTE / BUSCADOR IA
    - Pega el enunciado de cualquier problema o ejercicio.
    - Conectado a la API gratuita de Google Gemini con detección automática de modelos activos.
    - Incluye Analizador Heurístico Experto para respaldo instantáneo.
    - Te dice qué método usar, por qué, qué orden tiene y qué valor poner en cada casilla.
    - ¡Botón de 1 clic para cargar todos los datos directamente en el método!
"""

import ast
import json
import math
import re
import threading
import tkinter as tk
from dataclasses import dataclass, field
from decimal import ROUND_HALF_UP, Decimal
from fractions import Fraction
from tkinter import font as tkfont
from tkinter import messagebox, ttk
import urllib.request
import urllib.error
import ssl

# API Key predeterminada configurada para el usuario
API_KEY_PREDETERMINADA = "AQ.Ab8RN6I_LDkNMtNS7sFqlzLXJClmrhjbFqqITXqst6Zo5cfNYg"

# ======================================================================
# PALETA DE COLORES
# Idea visual: tinta azul oscura sobre papel frío, con un único acento
# verde azulado para lo importante (botón, resultado, curva aproximada).
# ======================================================================
C = {
    "tinta": "#10253A",         # barra lateral y texto principal
    "tinta_2": "#1B3A57",       # hover de la barra lateral
    "tinta_texto": "#CFE0EE",   # texto secundario sobre la tinta
    "papel": "#EDF2F6",         # fondo de la ventana
    "tarjeta": "#FFFFFF",       # fondo de las tarjetas
    "linea": "#D5DEE6",         # bordes finos
    "acento": "#0B7A83",        # acento principal
    "acento_osc": "#075E66",    # acento al pasar el mouse / títulos
    "acento_suave": "#DDF0F1",  # fondo de la fórmula
    "texto": "#16283A",         # texto normal
    "apagado": "#5D7186",       # texto secundario
    "ok": "#0B7A5A",
    "ok_suave": "#E0F4EC",
    "error": "#B42318",
    "error_suave": "#FCE8E6",
    "aviso": "#9A5B00",
    "aviso_suave": "#FFF1D6",
    "curva": "#10253A",         # curva de f(x) en la gráfica
    "area": "#BFE3E6",          # relleno de la aproximación
    "euler": "#C2410C",         # serie de Euler en la gráfica
    "exacta": "#0B7A5A",        # solución exacta en la gráfica
    "ia_morado": "#4F46E5",     # acento distintivo del Asistente IA
    "ia_suave": "#EEF2FF",      # fondo para recomendaciones IA
}


# ======================================================================
# 1. EVALUADOR SEGURO DE FUNCIONES ESCRITAS COMO TEXTO
# ======================================================================
class ErrorMatematico(Exception):
    """Se lanza cuando algo NO se puede calcular. El mensaje explica la razón."""


_FUNCIONES = {
    "sin": math.sin, "cos": math.cos, "tan": math.tan,
    "asin": math.asin, "acos": math.acos, "atan": math.atan,
    "sinh": math.sinh, "cosh": math.cosh, "tanh": math.tanh,
    "exp": math.exp, "log": math.log, "log10": math.log10, "log2": math.log2,
    "sqrt": math.sqrt, "abs": abs, "erf": math.erf,
}
_CONSTANTES = {"pi": math.pi, "e": math.e}
_ALIAS = {
    "sen": "sin", "senh": "sinh", "tg": "tan", "arcsen": "asin",
    "arcsin": "asin", "arccos": "acos", "arctan": "atan",
    "ln": "log", "raiz": "sqrt",
}
_NODOS_OK = (
    ast.Expression, ast.BinOp, ast.UnaryOp, ast.Call, ast.Name, ast.Constant,
    ast.Load, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow, ast.USub, ast.UAdd,
)


def _preparar(texto):
    """Convierte la notación 'de cuaderno' en sintaxis de Python."""
    t = texto.strip().lower()
    for viejo, nuevo in (("π", "pi"), ("^", "**"), ("×", "*"), ("÷", "/"),
                         ("−", "-"), ("–", "-"), ("·", "*")):
        t = t.replace(viejo, nuevo)
    t = re.sub(r"(?<=\d),(?=\d)", ".", t)
    patron = r"\b(" + "|".join(sorted(_ALIAS, key=len, reverse=True)) + r")\b"
    t = re.sub(patron, lambda m: _ALIAS[m.group(1)], t)
    t = re.sub(r"(?<![\w.])(\d+\.?\d*|\.\d+)(?!\s*[eE][+-]?\d)\s*(?=[a-zA-Z_(])", r"\1*", t)
    t = re.sub(r"\)\s*(?=[\w(])", ")*", t)
    return t


def _separar_variables(t, variables):
    """Multiplicación implícita entre variables: xy -> x*y  (así se puede escribir 2xy como en el PDF)."""
    def reparar(m):
        nombre = m.group(0)
        if nombre in variables or nombre in _CONSTANTES or nombre in _FUNCIONES:
            return nombre
        if variables and all(c in variables for c in nombre):
            return "*".join(nombre)
        return nombre
    return re.sub(r"[a-z_][a-z_0-9]*", reparar, t)


def compilar_expresion(texto, variables=("x",)):
    """
    Devuelve una función de Python lista para evaluar.
        f = compilar_expresion("x^2 + 1")      ->  f(3) == 10.0
        g = compilar_expresion("x + y", ("x", "y"))  ->  g(1, 2) == 3.0
    Si la expresión no es válida lanza ErrorMatematico con una explicación.
    """
    if texto is None or not str(texto).strip():
        raise ErrorMatematico("Hay un cuadro vacío: escribe la expresión (por ejemplo x^2 + 1).")
    preparado = _separar_variables(_preparar(str(texto)), variables)
    try:
        arbol = ast.parse(preparado, mode="eval")
    except SyntaxError:
        raise ErrorMatematico(
            f"No pude entender «{texto}». Revisa los paréntesis y los operadores: "
            "usa * para multiplicar y ^ (o **) para las potencias."
        ) from None

    for nodo in ast.walk(arbol):
        if not isinstance(nodo, _NODOS_OK):
            raise ErrorMatematico(
                f"«{texto}» contiene algo que no se puede usar. Solo se permiten números, "
                f"{', '.join(variables) if variables else 'constantes'}, las operaciones + - * / ^ "
                "y funciones como sen, cos, tan, exp, ln, sqrt."
            )
        if isinstance(nodo, ast.Constant):
            if type(nodo.value) not in (int, float):
                raise ErrorMatematico(f"«{texto}» contiene un valor que no es numérico.")
            nodo.value = float(nodo.value)
        if isinstance(nodo, ast.Call):
            if not isinstance(nodo.func, ast.Name) or nodo.func.id not in _FUNCIONES or nodo.keywords:
                nombre = nodo.func.id if isinstance(nodo.func, ast.Name) else "?"
                raise ErrorMatematico(
                    f"La función «{nombre}» no existe. Disponibles: sen, cos, tan, exp, ln, log10, sqrt, abs, erf."
                )
        if isinstance(nodo, ast.Name):
            if nodo.id not in variables and nodo.id not in _CONSTANTES and nodo.id not in _FUNCIONES:
                permitido = f"la variable {' y '.join(variables)}" if variables else "números y constantes (pi, e)"
                raise ErrorMatematico(
                    f"«{nodo.id}» no se reconoce. Aquí solo puedes usar {permitido}."
                )

    codigo = compile(arbol, "<expresion>", "eval")

    def evaluar(*valores):
        entorno = dict(_CONSTANTES)
        entorno.update(_FUNCIONES)
        entorno.update(zip(variables, valores))
        donde = ", ".join(f"{n} = {v:.6g}" for n, v in zip(variables, valores))
        motivo = None
        resultado = None
        try:
            resultado = eval(codigo, {"__builtins__": {}}, entorno)
        except ZeroDivisionError:
            motivo = "hay una división entre cero"
        except ValueError:
            motivo = "queda fuera del dominio de la función (por ejemplo, raíz o logaritmo de un número negativo)"
        except OverflowError:
            motivo = "el resultado es demasiado grande para representarse"
        except TypeError:
            motivo = "la expresión no se pudo calcular (cada función necesita su argumento: sen(x), exp(x)...)"
        if motivo is None:
            if isinstance(resultado, complex):
                motivo = "el resultado es un número complejo (raíz o potencia fraccionaria de un negativo)"
            elif not isinstance(resultado, (int, float)):
                motivo = "no devuelve un número"
            else:
                resultado = float(resultado)
                if math.isnan(resultado) or math.isinf(resultado):
                    motivo = "el resultado no es finito (infinito o indefinido)"
        if motivo:
            lugar = f" en {donde}" if donde else ""
            raise ErrorMatematico(f"No se puede evaluar la expresión{lugar}: {motivo}.")
        return resultado

    evaluar.texto = preparado.replace("**", "^")
    evaluar.arbol = arbol
    return evaluar


class _Conv:
    _FUNC = {"sin": "sen", "cos": "cos", "tan": "tg", "asin": "arcsen", "acos": "arccos", "atan": "arctg",
             "sinh": "senh", "cosh": "cosh", "tanh": "tgh", "log": "ln", "log10": "log", "log2": "log", "erf": "erf"}
    _TRIG = {"sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "log", "log10", "log2", "erf"}

    def __init__(self, modo, valores=None, dec=6):
        self.tex = modo == "tex"
        self.valores = valores
        self.dec = dec

    @staticmethod
    def _prec(n):
        if isinstance(n, ast.BinOp):
            if isinstance(n.op, (ast.Add, ast.Sub)):
                return 1
            if isinstance(n.op, (ast.Mult, ast.Div)):
                return 2
            return 4
        if isinstance(n, ast.UnaryOp):
            return 3
        return 5

    @staticmethod
    def _es_num(n):
        return isinstance(n, ast.Constant)

    def _num(self, v):
        s = str(int(v)) if v == int(v) and abs(v) < 1e15 else f"{v:.10g}"
        if "e" in s:
            m, e = s.split("e")
            return f"{m}\\cdot 10^{{{int(e)}}}" if self.tex else f"{m}·10^{{{int(e)}}}"
        return s

    def _paren(self, s):
        if self.tex and any(t in s for t in ("\\frac", "\\sqrt", "\\sum", "\\int")):
            return "\\left(" + s + "\\right)"
        return "(" + s + ")"

    def conv(self, n):
        if isinstance(n, ast.Constant):
            return self._num(n.value)
        if isinstance(n, ast.Name):
            if self.valores is not None and n.id in self.valores:
                return pc(self.valores[n.id], self.dec)
            if n.id == "pi":
                return "\\pi" if self.tex else "π"
            return n.id
        if isinstance(n, ast.UnaryOp):
            s = self.conv(n.operand)
            if isinstance(n.op, ast.UAdd):
                return s
            if self._prec(n.operand) <= 1:
                s = self._paren(s)
            return "−" + s
        if isinstance(n, ast.BinOp):
            return self._bin(n)
        if isinstance(n, ast.Call):
            return self._llamada(n)
        return "?"

    def _bin(self, n):
        op = type(n.op)
        if op is ast.Add:
            return f"{self.conv(n.left)} + {self.conv(n.right)}"
        if op is ast.Sub:
            r = self.conv(n.right)
            if self._prec(n.right) <= 1:
                r = self._paren(r)
            return f"{self.conv(n.left)} − {r}"
        if op is ast.Mult:
            return self._mult(n)
        if op is ast.Div:
            a, b = self.conv(n.left), self.conv(n.right)
            if self.tex:
                return "\\frac{" + a + "}{" + b + "}"
            if self._prec(n.left) < 2:
                a = self._paren(a)
            if self._prec(n.right) <= 2:
                b = self._paren(b)
            return a + "/" + b
        return self._pot(n)

    def _mult(self, n):
        izq, der = n.left, n.right
        l, r = self.conv(izq), self.conv(der)
        if self._prec(izq) < 2:
            l = self._paren(l)
        if self._prec(der) < 2 or isinstance(der, ast.UnaryOp):
            r = self._paren(r)
        if self.valores is not None or self._es_num(der):
            sep = " \\cdot " if self.tex else "·"
        elif self._es_num(izq):
            sep = ""
        else:
            sep = "\\," if self.tex else ""
        return l + sep + r

    def _pot(self, n):
        base, exp = n.left, n.right
        e = self.conv(exp)
        if isinstance(base, ast.Call) and isinstance(base.func, ast.Name) and base.func.id in self._TRIG:
            return self._llamada(base, e)
        b = self.conv(base)
        if not isinstance(base, (ast.Name, ast.Constant)):
            b = self._paren(b)
        return b + "^{" + e + "}"

    def _llamada(self, n, potencia=None):
        nombre = n.func.id
        a = ", ".join(self.conv(x) for x in n.args)
        if nombre == "sqrt":
            return ("\\sqrt{" + a + "}") if self.tex else ("√(" + a + ")")
        if nombre == "exp":
            return "e^{" + a + "}"
        if nombre == "abs":
            return ("\\left|" + a + "\\right|") if self.tex else ("|" + a + "|")
        nom = self._FUNC.get(nombre, nombre)
        cab = ("\\" + nom) if self.tex else nom
        if nombre in ("log10", "log2"):
            cab += "_{" + nombre[3:] + "}"
        if potencia is not None:
            cab += "^{" + potencia + "}"
        return cab + self._paren(a)


def a_tex(texto, variables=("x",), envolver=False):
    f = compilar_expresion(texto, variables)
    s = _Conv("tex").conv(f.arbol.body)
    if envolver and _Conv._prec(f.arbol.body) <= 1:
        s = "\\left(" + s + "\\right)"
    return s


def bonita(texto, variables=("x",)):
    try:
        return _Conv("lineal").conv(compilar_expresion(texto, variables).arbol.body)
    except ErrorMatematico:
        return str(texto)


# ======================================================================
# 2. UTILIDADES: FORMATO Y LECTURA DE DATOS
# ======================================================================
def fmt(v, dec=6):
    if v is None:
        return "—"
    if v == 0:
        return f"{0:.{dec}f}"
    if abs(v) >= 1e12 or abs(v) < 0.5 * 10 ** (-dec):
        return f"{v:.{max(dec - 1, 1)}e}"
    return f"{v:.{dec}f}"


def g(v):
    return f"{v:.10g}"


def termino(v, dec):
    s = fmt(v, dec)
    return f"({s})" if v < 0 else s


def suma_texto(valores, dec, maximo=8):
    if not valores:
        return "0"
    textos = [termino(v, dec) for v in valores]
    if len(textos) > maximo:
        textos = textos[:maximo - 2] + ["…"] + textos[-1:]
    return " + ".join(textos)


_RE_INDICE = re.compile(r"(?<![A-Za-zÀ-ÿ_.])([xykWtSAhȳ])(\d+|i\+1|n[−-]1|i|n|j)(?![A-Za-zÀ-ÿ0-9])")
_SUBS = str.maketrans("0123456789+-−ijn", "₀₁₂₃₄₅₆₇₈₉₊₋₋ᵢⱼₙ")


def _enc_bonito(texto):
    return _RE_INDICE.sub(lambda m: m.group(1) + m.group(2).translate(_SUBS), texto)


def _auto_indices(seg):
    trozos, pos = [], 0
    for m in _RE_INDICE.finditer(seg):
        trozos.append((seg[pos:m.start()] + m.group(1), None))
        trozos.append((m.group(2), "sub1"))
        pos = m.end()
    trozos.append((seg[pos:], None))
    return [t for t in trozos if t[0]]


def partir_marcado(texto, autoindices=True, nivel=0):
    trozos, actual, i = [], "", 0
    while i < len(texto):
        c = texto[i]
        if c in "^_" and i + 1 < len(texto) and texto[i + 1] == "{":
            prof, j = 0, i + 1
            while j < len(texto):
                if texto[j] == "{":
                    prof += 1
                elif texto[j] == "}":
                    prof -= 1
                    if prof == 0:
                        break
                j += 1
            interior = texto[i + 2:j]
            if actual:
                trozos += _auto_indices(actual) if (autoindices and nivel == 0) else [(actual, None)]
                actual = ""
            if c == "^":
                etiqueta = "sup1" if nivel == 0 else "sup2"
                for t, e in partir_marcado(interior, False, nivel + 1):
                    trozos.append((t, e or etiqueta))
            else:
                trozos.append((interior, "sub1"))
            i = j + 1
        else:
            actual += c
            i += 1
    if actual:
        trozos += _auto_indices(actual) if (autoindices and nivel == 0) else [(actual, None)]
    return trozos


def leer_numero(texto, nombre):
    if texto is None or not str(texto).strip():
        raise ErrorMatematico(f"Falta el valor de «{nombre}».")
    try:
        return compilar_expresion(texto, variables=())()
    except ErrorMatematico as e:
        raise ErrorMatematico(f"«{nombre}» no es un número válido ({texto}). {e}") from None


def leer_entero(texto, nombre, minimo=1, maximo=100000):
    v = leer_numero(texto, nombre)
    if abs(v - round(v)) > 1e-9:
        raise ErrorMatematico(f"«{nombre}» debe ser un número entero (escribiste {texto}).")
    v = int(round(v))
    if v < minimo:
        raise ErrorMatematico(f"«{nombre}» debe ser al menos {minimo} (escribiste {v}).")
    if v > maximo:
        raise ErrorMatematico(f"«{nombre}» es demasiado grande ({v}); el máximo permitido es {maximo}.")
    return v


def leer_lista(texto, nombre):
    partes = [p for p in re.split(r"[,;\s]+", (texto or "").strip()) if p]
    if not partes:
        raise ErrorMatematico(f"Falta la lista «{nombre}».")
    return [leer_numero(p, nombre) for p in partes]


def _validar_intervalo(a, b):
    if a == b:
        raise ErrorMatematico(
            "Los límites a y b son iguales: el intervalo tiene longitud cero, la integral vale 0 "
            "y no hay nada que aproximar."
        )


def _es_constante(hs):
    return all(abs(x - hs[0]) <= 1e-9 * max(1.0, abs(hs[0])) for x in hs)


# ======================================================================
# 3. ESTRUCTURAS PARA EL RESULTADO Y EL PASO A PASO
# ======================================================================
class Pasos(list):
    def titulo(self, t):
        self.append(("titulo", t))

    def texto(self, t):
        self.append(("texto", t))

    def formula(self, t):
        self.append(("formula", t))

    def resultado(self, t):
        self.append(("resultado", t))

    def aviso(self, t):
        self.append(("aviso", t))


@dataclass
class Resultado:
    etiqueta: str
    valor: str
    pasos: list
    cols: list = field(default_factory=list)
    filas: list = field(default_factory=list)
    grafica: dict = None
    avisos: list = field(default_factory=list)


def _comparar_exacto(d, valor, p, F):
    texto = (d.get("exacto") or "").strip()
    if not texto:
        return
    exacto = leer_numero(texto, "Valor exacto")
    err = abs(exacto - valor)
    p.titulo("Comparación con el valor exacto")
    p.formula(f"Error absoluto = |exacto − aproximado| = |{F(exacto)} − {F(valor)}| = {F(err)}")
    if exacto != 0:
        p.formula(f"Error relativo = {err / abs(exacto) * 100:.6g} %")


def _listar_nodos(p, xs, ys, F, maximo=12):
    n = len(xs)
    if n <= maximo:
        indices = list(range(n))
    else:
        indices = list(range(maximo - 3)) + [None, n - 2, n - 1]
    for i in indices:
        if i is None:
            p.formula("   ⋮   (la pestaña «Tabla de valores» muestra todos los nodos)")
        else:
            p.formula(f"x{i} = {F(xs[i])}      f(x{i}) = {F(ys[i])}")


def muestrear(f, a, b, N=240):
    pts = []
    for i in range(N + 1):
        x = a + (b - a) * i / N
        try:
            pts.append((x, f(x)))
        except ErrorMatematico:
            pass
    return pts


def lagrange(xs, ys, x):
    total = 0.0
    for i in range(len(xs)):
        t = ys[i]
        for j in range(len(xs)):
            if j != i:
                t *= (x - xs[j]) / (xs[i] - xs[j])
        total += t
    return total


def capas_area_por_grupos(xs, ys, m):
    capas = []
    grupos = (len(xs) - 1) // m
    if grupos > 60:
        poligono = [(xs[0], 0)] + list(zip(xs, ys)) + [(xs[-1], 0)]
        return [dict(tipo="area", pts=poligono, relleno=C["area"], borde=C["acento"])]
    for k in range(grupos):
        gx, gy = xs[k * m:k * m + m + 1], ys[k * m:k * m + m + 1]
        if m == 1:
            curva = [(gx[0], gy[0]), (gx[1], gy[1])]
        else:
            N = 24
            curva = []
            for j in range(N + 1):
                x = gx[0] + (gx[-1] - gx[0]) * j / N
                curva.append((x, lagrange(gx, gy, x)))
        poligono = [(gx[0], 0)] + curva + [(gx[-1], 0)]
        capas.append(dict(tipo="area", pts=poligono, relleno=C["area"], borde=C["acento"]))
    return capas


def grafica_integral(ctx, capas_area, titulo):
    capas = list(capas_area)
    if ctx["f"] is not None:
        capas.append(dict(tipo="linea", pts=muestrear(ctx["f"], ctx["a"], ctx["b"]),
                          color=C["curva"], ancho=2, leyenda="f(x)"))
    else:
        capas.append(dict(tipo="linea", pts=list(zip(ctx["xs"], ctx["ys"])),
                          color=C["apagado"], ancho=1, punteado=True, leyenda="datos"))
    if len(ctx["xs"]) <= 200:
        capas.append(dict(tipo="puntos", pts=list(zip(ctx["xs"], ctx["ys"])), color=C["acento_osc"]))
    return dict(titulo=titulo, capas=capas)


# ======================================================================
# 4. MÉTODOS DE INTEGRACIÓN
# ======================================================================
def leer_tabla(d):
    xs = leer_lista(d["xs"], "Valores de x")
    ys = leer_lista(d["ys"], "Valores de f(x)")
    if len(xs) != len(ys):
        raise ErrorMatematico(
            f"Hay {len(xs)} valores de x pero {len(ys)} de f(x): deben ser la misma cantidad. "
            "(Separa los números con espacios o comas y usa punto para los decimales.)"
        )
    if len(xs) < 2:
        raise ErrorMatematico("La tabla necesita al menos 2 puntos.")
    for i in range(1, len(xs)):
        if xs[i] <= xs[i - 1]:
            raise ErrorMatematico(
                f"Los valores de x deben ir de menor a mayor y sin repetirse "
                f"(revisa x{i - 1} = {g(xs[i - 1])} y x{i} = {g(xs[i])})."
            )
    desde = leer_numero(d["ta"], "Desde x") if (d.get("ta") or "").strip() else xs[0]
    hasta = leer_numero(d["tb"], "Hasta x") if (d.get("tb") or "").strip() else xs[-1]

    def buscar(v, nombre):
        for i, x in enumerate(xs):
            if abs(x - v) <= 1e-9 * max(1.0, abs(v)):
                return i
        raise ErrorMatematico(
            f"«{nombre}» = {g(v)} no aparece en la columna de x de la tabla. Con datos tabulados "
            "solo se puede integrar entre valores de x que existan en la tabla."
        )

    i0, i1 = buscar(desde, "Desde x"), buscar(hasta, "Hasta x")
    if i0 >= i1:
        raise ErrorMatematico("«Desde x» debe ser menor que «Hasta x».")
    return xs[i0:i1 + 1], ys[i0:i1 + 1]


def _malla_equiespaciada(d, regla_n, nombre):
    if d["modo"] == "tabla":
        xs, ys = leer_tabla(d)
        n = len(xs) - 1
        hs = [xs[i + 1] - xs[i] for i in range(n)]
        if not _es_constante(hs):
            ejemplo = ", ".join(g(h) for h in hs[:6]) + (" …" if len(hs) > 6 else "")
            raise ErrorMatematico(
                f"No se puede aplicar {nombre} a estos datos: los valores de x NO están igualmente "
                f"espaciados (los pasos entre puntos son {ejemplo}). Esta fórmula se deduce suponiendo "
                "un paso h constante (xi = x0 + i·h). Con espaciado desigual solo sirve el método del "
                "Trapecio compuesto, que suma el área de cada trapecio por separado."
            )
        mensaje = regla_n(n)
        if mensaje:
            raise ErrorMatematico(
                f"Tu tabla tiene {n + 1} puntos, es decir, {n} subintervalos. {mensaje} "
                "Agrega o quita puntos de la tabla, o usa el Trapecio."
            )
        return dict(xs=xs, ys=ys, h=hs[0], n=n, f=None, a=xs[0], b=xs[-1],
                    desc=f"Tabla con {n + 1} puntos ({n} subintervalos), de x = {g(xs[0])} a x = {g(xs[-1])}.")
    f = compilar_expresion(d["f"])
    a = leer_numero(d["a"], "a")
    b = leer_numero(d["b"], "b")
    _validar_intervalo(a, b)
    n = leer_entero(d["n"], "n (subintervalos)")
    mensaje = regla_n(n)
    if mensaje:
        raise ErrorMatematico(mensaje)
    h = (b - a) / n
    xs = [a + i * h for i in range(n + 1)]
    xs[-1] = b
    ys = [f(x) for x in xs]
    return dict(xs=xs, ys=ys, h=h, n=n, f=f, a=a, b=b,
                desc=f"f(x) = {bonita(d['f'])},   a = {g(a)},   b = {g(b)},   n = {n}")


def _paso_h(p, ctx, F):
    p.titulo("Paso 1: tamaño de paso h")
    if ctx["f"] is not None:
        p.formula(f"h = (b − a) / n = ({F(ctx['b'])} − {F(ctx['a'])}) / {ctx['n']} = {F(ctx['h'])}")
    else:
        p.formula(f"h = x1 − x0 = {F(ctx['h'])}   (la tabla ya trae los x igualmente espaciados)")


def _tabla_nodos(ctx, coefs, F):
    cols = ["i", "xi", "f(xi)", "coeficiente"]
    filas = [(i, F(ctx["xs"][i]), F(ctx["ys"][i]), c) for i, c in enumerate(coefs)]
    return cols, filas


def _final_integral(r, ctx, valor, d, p, F, avisos):
    p.titulo("Resultado")
    p.resultado(f"I ≈ {F(valor)}")
    _comparar_exacto(d, valor, p, F)
    if ctx["a"] > ctx["b"]:
        avisos.append("a es mayor que b: el resultado es el negativo de la integral de b a a.")
    for av in avisos:
        p.aviso(av)
    r.avisos = avisos
    return r


def metodo_trapecio(d):
    F = lambda v: fmt(v, d["dec"])
    p = Pasos()
    avisos = []
    p.titulo("Datos del problema")
    if d["modo"] == "tabla":
        xs, ys = leer_tabla(d)
        n = len(xs) - 1
        hs = [xs[i + 1] - xs[i] for i in range(n)]
        ctx = dict(xs=xs, ys=ys, f=None, a=xs[0], b=xs[-1], n=n)
        p.texto(f"Tabla con {n + 1} puntos ({n} subintervalos), de x = {g(xs[0])} a x = {g(xs[-1])}.")
    else:
        f = compilar_expresion(d["f"])
        a, b = leer_numero(d["a"], "a"), leer_numero(d["b"], "b")
        _validar_intervalo(a, b)
        n = leer_entero(d["n"], "n (subintervalos)")
        h = (b - a) / n
        xs = [a + i * h for i in range(n + 1)]
        xs[-1] = b
        ys = [f(x) for x in xs]
        hs = [h] * n
        ctx = dict(xs=xs, ys=ys, f=f, a=a, b=b, n=n, h=h)
        p.texto(f"f(x) = {bonita(d['f'])},   a = {g(a)},   b = {g(b)},   n = {n}")

    if _es_constante(hs):
        h = hs[0]
        ctx["h"] = h
        _paso_h(p, ctx, F)
        p.titulo("Paso 2: evaluar f(x) en los nodos xi = a + i·h")
        _listar_nodos(p, xs, ys, F)
        if n == 1:
            valor = h / 2 * (ys[0] + ys[1])
            p.titulo("Paso 3: fórmula del trapecio simple (ecuación 1)")
            p.formula("I = h/2 · [ f(x0) + f(x1) ]")
            p.formula(f"I = {F(h)}/2 · [ {termino(ys[0], d['dec'])} + {termino(ys[1], d['dec'])} ]")
            p.formula("Otra forma (ecuación 2):  I = (b − a)/2 · [ f(xa) + f(xb) ]   (es lo mismo, con h = b − a)")
            coefs = [1, 1]
        else:
            interior = ys[1:-1]
            suma = math.fsum(interior)
            valor = h / 2 * (ys[0] + 2 * suma + ys[-1])
            p.titulo(f"Paso 3: sumar los nodos interiores (i = 1 … {n - 1})")
            p.formula(f"Σ f(xi) = {suma_texto(interior, d['dec'])} = {F(suma)}")
            p.titulo("Paso 4: fórmula del trapecio compuesto (ecuación 8)")
            p.formula("I = h/2 · [ f(x0) + 2·Σ f(xi) + f(xn) ]")
            p.formula(f"I = {F(h)}/2 · [ {termino(ys[0], d['dec'])} + 2·({F(suma)}) + {termino(ys[-1], d['dec'])} ]")
            coefs = [1] + [2] * (n - 1) + [1]
        cols, filas = _tabla_nodos(ctx, coefs, F)
    else:
        p.titulo("Paso 1: anchos de cada subintervalo")
        p.texto("Los x no están igualmente espaciados, así que no existe un único h. El método sigue "
                "siendo el mismo: se calcula el área de cada trapecio con su propio ancho hi = xi+1 − xi "
                "y se suman.")
        p.titulo("Paso 2: área de cada trapecio  Ai = hi/2 · [ f(xi) + f(xi+1) ]")
        areas = [hs[i] / 2 * (ys[i] + ys[i + 1]) for i in range(n)]
        maximo = 12
        mostrar = list(range(n)) if n <= maximo else list(range(maximo - 2)) + [None, n - 1]
        for i in range(n):
            if i < maximo - 2 or i == n - 1:
                p.formula(f"A{i} = {F(hs[i])}/2 · [ {termino(ys[i], d['dec'])} + {termino(ys[i + 1], d['dec'])} ] = {F(areas[i])}")
            elif i == maximo - 2:
                p.formula("   ⋮")
        valor = math.fsum(areas)
        p.titulo("Paso 3: sumar todas las áreas")
        p.formula(f"I = A0 + A1 + … + A{n - 1} = {F(valor)}")
        cols = ["i", "xi", "f(xi)", "hi", "área Ai"]
        filas = [(i, F(xs[i]), F(ys[i]),
                  F(hs[i]) if i < n else "—", F(areas[i]) if i < n else "—") for i in range(n + 1)]

    grafica = grafica_integral(ctx, capas_area_por_grupos(xs, ys, 1), "Aproximación con trapecios")
    etiqueta = "Área bajo la curva" if d["modo"] == "tabla" else "Integral aproximada"
    r = Resultado(etiqueta, F(valor), p, cols, filas, grafica)
    return _final_integral(r, ctx, valor, d, p, F, avisos)


def metodo_simpson13(d):
    F = lambda v: fmt(v, d["dec"])

    def regla(n):
        if n < 2 or n % 2:
            sugerencia = ""
            if n % 3 == 0:
                sugerencia = " Con ese n sí puedes usar Simpson 3/8."
            return (f"Simpson 1/3 necesita un número PAR de subintervalos (2, 4, 6, …): cada parábola usa "
                    f"3 puntos y cubre 2 subintervalos, y con n = {n} quedaría uno suelto. "
                    f"Prueba con n = {max(n - 1, 2)} o n = {n + 1}.{sugerencia}")
        return None

    ctx = _malla_equiespaciada(d, regla, "Simpson 1/3")
    xs, ys, h, n = ctx["xs"], ctx["ys"], ctx["h"], ctx["n"]
    p, avisos = Pasos(), []
    p.titulo("Datos del problema")
    p.texto(ctx["desc"])
    _paso_h(p, ctx, F)
    p.titulo("Paso 2: evaluar f(x) en los nodos xi = a + i·h")
    _listar_nodos(p, xs, ys, F)

    impares = ys[1:n:2]
    pares = ys[2:n - 1:2]
    S4, S2 = math.fsum(impares), math.fsum(pares)
    valor = h / 3 * (ys[0] + 4 * S4 + 2 * S2 + ys[-1])

    if n == 2:
        p.titulo("Paso 3: fórmula de Simpson 1/3 simple (ecuación 3)")
        p.formula("I = h/3 · [ f(x0) + 4·f(x1) + f(x2) ]")
        p.formula(f"I = {F(h)}/3 · [ {termino(ys[0], d['dec'])} + 4·({termino(ys[1], d['dec'])}) + {termino(ys[2], d['dec'])} ]")
    else:
        p.titulo("Paso 3: sumas de los nodos interiores")
        p.formula(f"Σ impares (i = 1, 3, …, {n - 1}), coeficiente 4:  {suma_texto(impares, d['dec'])} = {F(S4)}")
        p.formula(f"Σ pares   (i = 2, 4, …, {n - 2}), coeficiente 2:  {suma_texto(pares, d['dec'])} = {F(S2)}")
        p.titulo("Paso 4: fórmula de Simpson 1/3 compuesta (ecuación 9)")
        p.formula("I = h/3 · [ f(x0) + 4·Σ impares + 2·Σ pares + f(xn) ]")
        p.formula(f"I = {F(h)}/3 · [ {termino(ys[0], d['dec'])} + 4·({F(S4)}) + 2·({F(S2)}) + {termino(ys[-1], d['dec'])} ]")

    coefs = [1] + [4 if i % 2 else 2 for i in range(1, n)] + [1]
    cols, filas = _tabla_nodos(ctx, coefs, F)
    grafica = grafica_integral(ctx, capas_area_por_grupos(xs, ys, 2), "Aproximación con parábolas")
    etiqueta = "Área bajo la curva" if ctx["f"] is None else "Integral aproximada"
    r = Resultado(etiqueta, F(valor), p, cols, filas, grafica)
    return _final_integral(r, ctx, valor, d, p, F, avisos)


def metodo_simpson38(d):
    F = lambda v: fmt(v, d["dec"])

    def regla(n):
        if n < 3 or n % 3:
            sugerencia = " Con ese n sí puedes usar Simpson 1/3." if n % 2 == 0 else ""
            sig = ((n // 3) + 1) * 3 if n >= 3 else 3
            return (f"Simpson 3/8 necesita que n sea múltiplo de 3 (3, 6, 9, …): cada cúbica usa 4 puntos "
                    f"y cubre 3 subintervalos. Con n = {n} sobrarían subintervalos sueltos. "
                    f"Prueba con n = {sig}.{sugerencia}")
        return None

    ctx = _malla_equiespaciada(d, regla, "Simpson 3/8")
    xs, ys, h, n = ctx["xs"], ctx["ys"], ctx["h"], ctx["n"]
    p, avisos = Pasos(), []
    p.titulo("Datos del problema")
    p.texto(ctx["desc"])
    _paso_h(p, ctx, F)
    p.titulo("Paso 2: evaluar f(x) en los nodos xi = a + i·h")
    _listar_nodos(p, xs, ys, F)

    S1 = ys[1:n - 1:3]
    S2 = ys[2:n:3]
    S3 = ys[3:n - 2:3]
    s1, s2, s3 = math.fsum(S1), math.fsum(S2), math.fsum(S3)
    valor = 3 * h / 8 * (ys[0] + 3 * s1 + 3 * s2 + 2 * s3 + ys[-1])

    if n == 3:
        p.titulo("Paso 3: fórmula de Simpson 3/8 simple (ecuación 4)")
        p.formula("I = 3h/8 · [ f(x0) + 3·f(x1) + 3·f(x2) + f(x3) ]")
        p.formula(f"I = 3·{F(h)}/8 · [ {termino(ys[0], d['dec'])} + 3·({termino(ys[1], d['dec'])}) + "
                  f"3·({termino(ys[2], d['dec'])}) + {termino(ys[3], d['dec'])} ]")
    else:
        p.titulo("Paso 3: sumas de los nodos interiores")
        p.formula(f"S1 (i = 1, 4, …, {n - 2}), coeficiente 3:  {suma_texto(S1, d['dec'])} = {F(s1)}")
        p.formula(f"S2 (i = 2, 5, …, {n - 1}), coeficiente 3:  {suma_texto(S2, d['dec'])} = {F(s2)}")
        p.formula(f"S3 (i = 3, 6, …, {n - 3}), coeficiente 2:  {suma_texto(S3, d['dec'])} = {F(s3)}")
        p.titulo("Paso 4: fórmula de Simpson 3/8 compuesta (ecuación 10)")
        p.formula("I = 3h/8 · [ f(x0) + 3·S1 + 3·S2 + 2·S3 + f(xn) ]")
        p.formula(f"I = 3·{F(h)}/8 · [ {termino(ys[0], d['dec'])} + 3·({F(s1)}) + 3·({F(s2)}) + "
                  f"2·({F(s3)}) + {termino(ys[-1], d['dec'])} ]")

    coefs = [1] + [2 if i % 3 == 0 else 3 for i in range(1, n)] + [1]
    cols, filas = _tabla_nodos(ctx, coefs, F)
    grafica = grafica_integral(ctx, capas_area_por_grupos(xs, ys, 3), "Aproximación con cúbicas")
    etiqueta = "Área bajo la curva" if ctx["f"] is None else "Integral aproximada"
    r = Resultado(etiqueta, F(valor), p, cols, filas, grafica)
    return _final_integral(r, ctx, valor, d, p, F, avisos)


_NEWTON_COTES = {
    4: ("2h/45", 2 / 45, [7, 32, 12, 32, 7]),
    5: ("5h/288", 5 / 288, [19, 75, 50, 50, 75, 19]),
    6: ("h/140", 1 / 140, [41, 216, 27, 272, 27, 216, 41]),
}


def metodo_newton_cotes(d):
    F = lambda v: fmt(v, d["dec"])

    def regla(n):
        if n not in _NEWTON_COTES:
            return (f"El PDF trae las fórmulas de Newton-Cotes para n = 4, 5 y 6; con n = {n} no hay "
                    "fórmula en esta sección. (Para n = 1, 2 y 3 están el Trapecio, Simpson 1/3 y Simpson 3/8.)")
        return None

    ctx = _malla_equiespaciada(d, regla, "Newton-Cotes")
    xs, ys, h, n = ctx["xs"], ctx["ys"], ctx["h"], ctx["n"]
    texto_c, c, pesos = _NEWTON_COTES[n]
    p, avisos = Pasos(), []
    p.titulo("Datos del problema")
    p.texto(ctx["desc"])
    _paso_h(p, ctx, F)
    p.titulo("Paso 2: evaluar f(x) en los nodos xi = a + i·h")
    _listar_nodos(p, xs, ys, F)
    p.titulo(f"Paso 3: pesos de la fórmula para n = {n}")
    p.formula(f"I = {texto_c} · [ " + " + ".join(f"{w}·f(x{i})" for i, w in enumerate(pesos)) + " ]")
    suma = math.fsum(w * y for w, y in zip(pesos, ys))
    valor = c * h * suma
    p.titulo("Paso 4: sustituir")
    p.formula(f"Σ pesos·f(xi) = {F(suma)}")
    p.formula(f"I = {texto_c.replace('h', F(h))} · ({F(suma)})")

    cols, filas = _tabla_nodos(ctx, pesos, F)
    grafica = grafica_integral(ctx, capas_area_por_grupos(xs, ys, n), f"Polinomio de grado {n} por los nodos")
    etiqueta = "Área bajo la curva" if ctx["f"] is None else "Integral aproximada"
    r = Resultado(etiqueta, F(valor), p, cols, filas, grafica)
    return _final_integral(r, ctx, valor, d, p, F, avisos)


def _gauss_legendre(n):
    nodos, pesos = [], []
    for i in range(1, n + 1):
        t = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(100):
            p0, p1 = 1.0, t
            for k in range(2, n + 1):
                p0, p1 = p1, ((2 * k - 1) * t * p1 - (k - 1) * p0) / k
            dp = n * (t * p1 - p0) / (t * t - 1)
            paso = p1 / dp
            t -= paso
            if abs(paso) < 1e-15:
                break
        p0, p1 = 1.0, t
        for k in range(2, n + 1):
            p0, p1 = p1, ((2 * k - 1) * t * p1 - (k - 1) * p0) / k
        dp = n * (t * p1 - p0) / (t * t - 1)
        nodos.append(t)
        pesos.append(2 / ((1 - t * t) * dp * dp))
    pares = sorted(zip(nodos, pesos))
    return [0.0 if abs(t) < 1e-14 else t for t, _ in pares], [w for _, w in pares]


_GAUSS_MAX = 10
_TABLA1 = {
    2: ([-0.5773502692, 0.5773502692], [1.0, 1.0]),
    3: ([-0.774596, 0.0, 0.774596], [0.5555, 0.888888, 0.5555]),
    4: ([-0.8611363116, -0.3399810436, 0.3399810436, 0.8611363116],
        [0.347854, 0.6521451549, 0.6521451549, 0.347854]),
}
_PRECISION = ["Como la Tabla 1 del PDF", "Exactos (todos los decimales)", "Cortados a 4 decimales"]


def _truncar4(v):
    return math.trunc(v * 1e4) / 1e4


def metodo_gauss(d):
    dec = d["dec"]
    F = lambda v: fmt(v, dec)
    F10 = lambda v: fmt(v, 10)
    p, avisos = Pasos(), []
    f = compilar_expresion(d["f"])
    a, b = leer_numero(d["a"], "a"), leer_numero(d["b"], "b")
    _validar_intervalo(a, b)
    npts = leer_entero(d["npuntos"], "Número de puntos n", 1, 100000)
    if npts < 2 or npts > _GAUSS_MAX:
        raise ErrorMatematico(
            f"El programa calcula la cuadratura de Gauss con 2 a {_GAUSS_MAX} puntos (escribiste {npts}). "
            "La Tabla 1 del PDF trae 2, 3 y 4 puntos; de 5 a 10 los nodos se calculan como raíces del "
            "polinomio de Legendre."
        )
    exactos = _gauss_legendre(npts)
    precision = d.get("precision") or _PRECISION[0]
    if precision == _PRECISION[2]:
        nodos, pesos = [_truncar4(t) for t in exactos[0]], [_truncar4(w) for w in exactos[1]]
    elif precision == _PRECISION[1] or npts not in _TABLA1:
        nodos, pesos = exactos
    else:
        nodos, pesos = _TABLA1[npts]

    p.titulo("Datos del problema")
    p.texto(f"f(x) = {bonita(d['f'])},   a = {g(a)},   b = {g(b)},   {npts} puntos de Gauss")
    p.titulo("Paso 1: cambiar el intervalo [a, b] a [−1, 1]  (ecuaciones 20 y 21)")
    p.formula("x = [ (b − a)·t + (a + b) ] / 2          dx = (b − a)/2 · dt")
    factor = (b - a) / 2
    centro = (a + b) / 2
    p.formula(f"x = [ ({F(b)} − {F(a)})·t + ({F(a)} + {F(b)}) ] / 2 = {F(factor)}·t + {F(centro)}")
    p.formula(f"(b − a)/2 = {F(factor)}")
    p.titulo(f"Paso 2: nodos ti y pesos Wi para n = {npts}" + ("  (Tabla 1)" if npts in _TABLA1 else ""))
    if npts not in _TABLA1:
        p.texto("Estos nodos y pesos no están en la Tabla 1 del PDF (solo llega a 4 puntos): se calculan como las "
                "raíces del polinomio de Legendre de grado n y sus pesos asociados.")
    elif precision == _PRECISION[2]:
        p.texto("Se usan los nodos y pesos cortados a 4 decimales (por ejemplo 0.5773), como se escriben en una diapositiva.")
    elif precision == _PRECISION[1]:
        p.texto("Se usan los nodos y pesos con todos sus decimales (la Tabla 1 los trae recortados).")
    else:
        p.texto("Se usan los números tal como están impresos en la Tabla 1 del PDF.")
    for i, (t, w) in enumerate(zip(nodos, pesos), start=1):
        p.formula(f"t{i} = {F10(t)}      W{i} = {F10(w)}")

    p.titulo("Paso 3: evaluar f en los nodos  xi = factor·ti + centro")
    xs_n, fx, filas, terminos = [], [], [], []
    for i, (t, w) in enumerate(zip(nodos, pesos), start=1):
        x = factor * t + centro
        y = f(x)
        xs_n.append(x)
        fx.append(y)
        terminos.append(w * y)
        p.formula(f"x{i} = {F(factor)}·({F10(t)}) + {F(centro)} = {F(x)}      f(x{i}) = {F(y)}")
        filas.append((i, F10(t), F10(w), F(x), F(y), F(w * y)))
    suma = math.fsum(terminos)
    valor = factor * suma
    p.titulo("Paso 4: sumar y multiplicar por (b − a)/2  (ecuación 21)")
    p.formula("I ≈ (b − a)/2 · Σ Wi·f(xi)")
    p.formula(f"Σ Wi·f(xi) = {suma_texto(terminos, dec)} = {F(suma)}")
    p.formula(f"I ≈ {F(factor)} · {F(suma)}")
    p.texto(f"Con {npts} puntos la regla es exacta para polinomios de grado hasta 2n − 1 = {2 * npts - 1}.")

    ctx = dict(xs=xs_n, ys=fx, f=f, a=a, b=b)
    capas = [dict(tipo="area", pts=[(a, 0)] + muestrear(f, a, b) + [(b, 0)],
                  relleno=C["area"], borde=C["acento"])]
    for x, y in zip(xs_n, fx):
        capas.append(dict(tipo="linea", pts=[(x, 0), (x, y)], color=C["acento"], ancho=1, punteado=True))
    capas.append(dict(tipo="linea", pts=muestrear(f, a, b), color=C["curva"], ancho=2, leyenda="f(x)"))
    capas.append(dict(tipo="puntos", pts=list(zip(xs_n, fx)), color=C["acento_osc"]))
    grafica = dict(titulo="Nodos de Gauss sobre la curva", capas=capas)

    cols = ["i", "ti", "Wi", "xi", "f(xi)", "Wi·f(xi)"]
    r = Resultado("Integral aproximada", F(valor), p, cols, filas, grafica)
    return _final_integral(r, ctx, valor, d, p, F, avisos)


# ======================================================================
# 5. ECUACIONES DIFERENCIALES (CLASE 6): EULER, EULER MEJORADO Y RUNGE-KUTTA
# ======================================================================
def fc(v, dec):
    s = f"{v:.{dec}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def pc(v, dec):
    s = fc(v, dec)
    return f"({s})" if s.startswith("-") else s


def _sust(f, x, y, dec):
    return _Conv("lineal", {"x": x, "y": y}, dec).conv(f.arbol.body)


def _redondeador(d, dec):
    if not d.get("redondeo"):
        return lambda v: v
    unidad = Decimal(1).scaleb(-dec)

    def redondear(v):
        try:
            return float(Decimal(repr(round(v, 10))).quantize(unidad, rounding=ROUND_HALF_UP))
        except Exception:
            return v
    return redondear


def _leer_edo(d):
    f = compilar_expresion(d["f"], ("x", "y"))
    x0 = leer_numero(d["x0"], "x0")
    y0 = leer_numero(d["y0"], "y0")
    xf = leer_numero(d["xf"], "xf")
    if xf <= x0:
        raise ErrorMatematico(
            "El PDF trabaja en el intervalo [x0, xf] con h = (xf − x0)/n, así que xf debe ser MAYOR "
            f"que x0 (escribiste x0 = {g(x0)} y xf = {g(xf)})."
        )
    n = leer_entero(d["n"], "n (subintervalos)")
    h = (xf - x0) / n
    exacta = None
    if (d.get("exacta") or "").strip():
        exacta = compilar_expresion(d["exacta"], ("x",))
    xq, iq = None, None
    if (d.get("xq") or "").strip():
        xq = leer_numero(d["xq"], "x donde aproximar y")
        if xq < x0 - 1e-9 or xq > xf + 1e-9:
            raise ErrorMatematico(
                f"El x donde quieres aproximar y ({g(xq)}) debe estar dentro del intervalo [{g(x0)}, {g(xf)}]."
            )
        pos = (xq - x0) / h
        if abs(pos - round(pos)) > 1e-7:
            nodos = ", ".join(g(x0 + k * h) for k in range(min(n, 5) + 1)) + (", …" if n > 5 else "")
            raise ErrorMatematico(
                f"x = {g(xq)} no es uno de los puntos de la partición: el método solo calcula y en "
                f"xi = x0 + i·h, que con h = {g(h)} son ({nodos}). Cambia n (o x) para que {g(xq)} "
                "sea uno de esos puntos."
            )
        iq = int(round(pos))
    return dict(f=f, x0=x0, y0=y0, xf=xf, n=n, h=h, exacta=exacta, xq=xq, iq=iq)


def _evaluar_paso(f, i, *args):
    try:
        return f(*args)
    except ErrorMatematico as e:
        raise ErrorMatematico(f"Iteración {i + 1}: {e}") from None


def _vigilar(y, i, h):
    if not math.isfinite(y) or abs(y) > 1e150:
        raise ErrorMatematico(
            f"La solución se dispara en la iteración {i + 1} (|y| supera 10^150). Con h = {g(h)} el método "
            "diverge o la solución crece demasiado rápido. Prueba con más subintervalos (n mayor) o revisa f(x, y)."
        )


def _valor_exacto(exacta, x):
    try:
        return exacta(x)
    except ErrorMatematico as e:
        raise ErrorMatematico(f"Solución analítica: {e}") from None


def _paso_euler(a):
    f, x, y, h, i, R, dec, F = a["f"], a["x"], a["y"], a["h"], a["i"], a["R"], a["dec"], a["F"]
    k = _evaluar_paso(f, i, x, y)
    y_nuevo = R(y + h * k)
    linea = (f"y{i + 1} = y{i} + h·f(x{i}, y{i}) = {fc(y, dec)} + ({fc(h, dec)})·[{_sust(f, x, y, dec)}]"
             f" = {fc(y_nuevo, dec)}")
    return y_nuevo, [linea], [F(k)]


def _paso_heun(a):
    f, x, x1, y, h, i, R, dec, F = (a["f"], a["x"], a["x_sig"], a["y"], a["h"], a["i"], a["R"], a["dec"], a["F"])
    k1 = _evaluar_paso(f, i, x, y)
    y_barra = R(y + h * k1)
    k2 = _evaluar_paso(f, i, x1, y_barra)
    y_nuevo = R(y + h / 2 * (k1 + k2))
    lineas = [
        f"ȳ{i + 1} = y{i} + h·f(x{i}, y{i}) = {fc(y, dec)} + ({fc(h, dec)})·[{_sust(f, x, y, dec)}] = {fc(y_barra, dec)}",
        f"y{i + 1} = y{i} + h/2·[ f(x{i}, y{i}) + f(x{i + 1}, ȳ{i + 1}) ] = {fc(y, dec)} + {fc(h, dec)}/2·"
        f"[ ({_sust(f, x, y, dec)}) + ({_sust(f, x1, y_barra, dec)}) ] = {fc(y_nuevo, dec)}",
    ]
    return y_nuevo, lineas, [F(k1), F(y_barra), F(k2)]


_F = Fraction
_RK = {
    2: dict(c=[0, 1], a=[[], [1]], b=[1, 1], div=2,
            args=["xi, yi", "xi + h, yi + k1·h"]),
    3: dict(c=[0, 0.5, 1], a=[[], [0.5], [-1, 2]], b=[1, 4, 1], div=6,
            args=["xi, yi", "xi + h/2, yi + k1·h/2", "xi + h, yi − k1·h + 2k2·h"]),
    4: dict(c=[0, 0.5, 0.5, 1], a=[[], [0.5], [0, 0.5], [0, 0, 1]], b=[1, 2, 2, 1], div=6,
            args=["xi, yi", "xi + h/2, yi + k1·h/2", "xi + h/2, yi + k2·h/2", "xi + h, yi + k3·h"]),
    5: dict(c=[0, _F(1, 4), _F(1, 4), _F(1, 2), _F(3, 4), 1],
            a=[[], [_F(1, 4)], [_F(1, 8), _F(1, 8)], [0, _F(-1, 2), 1], [_F(3, 16), 0, 0, _F(9, 16)],
               [_F(-3, 7), _F(2, 7), _F(12, 7), _F(-12, 7), _F(8, 7)]],
            b=[7, 0, 32, 12, 32, 7], div=90,
            args=["xi, yi", "xi + h/4, yi + k1·h/4", "xi + h/4, yi + (k1 + k2)·h/8", "xi + h/2, yi − k2·h/2 + k3·h",
                  "xi + 3h/4, yi + (3k1 + 9k4)·h/16", "xi + h, yi + (−3k1 + 2k2 + 12k3 − 12k4 + 8k5)·h/7"]),
    6: dict(c=[0, _F(1, 3), _F(2, 3), _F(1, 3), _F(1, 2), _F(1, 2), 1],
            a=[[], [_F(1, 3)], [0, _F(2, 3)], [_F(1, 12), _F(1, 3), _F(-1, 12)],
               [_F(-1, 16), _F(9, 8), _F(-3, 16), _F(-3, 8)], [0, _F(9, 8), _F(-3, 8), _F(-3, 4), _F(1, 2)],
               [_F(9, 44), _F(-9, 11), _F(63, 44), _F(18, 11), 0, _F(-16, 11)]],
            b=[11, 0, 81, 81, -32, -32, 11], div=120,
            args=["xi, yi", "xi + h/3, yi + k1·h/3", "xi + 2h/3, yi + 2k2·h/3", "xi + h/3, yi + (k1 + 4k2 − k3)·h/12",
                  "xi + h/2, yi + (−k1 + 18k2 − 3k3 − 6k4)·h/16", "xi + h/2, yi + (9k2 − 3k3 − 6k4 + 4k5)·h/8",
                  "xi + h, yi + (9k1 − 36k2 + 63k3 + 72k4 − 64k6)·h/44"]),
}


def _suma_pesos(pesos, termino_k):
    txt = ""
    for n, (w, j) in enumerate(pesos):
        t = termino_k(abs(w), j)
        txt += (("−" if w < 0 else "") if n == 0 else (" − " if w < 0 else " + ")) + t
    return txt


def _formula_rk(o):
    rk = _RK[o]
    pesos = [(w, j) for j, w in enumerate(rk["b"]) if w != 0]
    simb = _suma_pesos(pesos, lambda m, j: f"{m}k{j + 1}" if m != 1 else f"k{j + 1}")
    eq = {2: "      (ecuación 3)", 3: "      (ecuación 4)", 4: "      (ecuación 5)"}.get(o, "      (orden extra: no está en el PDF)")
    return [f"yi+1 = yi + h/{rk['div']} · ({simb}){eq}"] + [f"k{j + 1} = f({a})" for j, a in enumerate(rk["args"])]


def _paso_rk(a):
    f, x, y, h, i, R, dec, F, orden = (a["f"], a["x"], a["y"], a["h"], a["i"], a["R"], a["dec"], a["F"], a["orden"])
    rk = _RK[orden]
    ks, lineas = [], []
    for j in range(len(rk["c"])):
        xa = x + rk["c"][j] * h
        ya = y + h * sum(coef * ks[l] for l, coef in enumerate(rk["a"][j]))
        k = _evaluar_paso(f, i, xa, ya)
        ks.append(k)
        argumentos = rk["args"][j].replace("xi", f"x{i}").replace("yi", f"y{i}")
        lineas.append(f"k{j + 1} = f({argumentos}) = f({fc(xa, dec)}, {fc(ya, dec)}) = "
                      f"[{_sust(f, xa, ya, dec)}] = {fc(k, dec)}")
    pesos = [(w, j) for j, w in enumerate(rk["b"]) if w != 0]
    y_nuevo = R(y + h / rk["div"] * sum(w * ks[j] for w, j in pesos))
    simb = _suma_pesos(pesos, lambda m, j: f"{m}k{j + 1}" if m != 1 else f"k{j + 1}")
    comb = _suma_pesos(pesos, lambda m, j: pc(ks[j], dec) if m == 1 else f"{m}·{pc(ks[j], dec)}")
    lineas.append(f"y{i + 1} = y{i} + h/{rk['div']}·({simb}) = {fc(y, dec)} + ({fc(h, dec)})/{rk['div']}·[{comb}]"
                  f" = {fc(y_nuevo, dec)}")
    return y_nuevo, lineas, [F(k) for k in ks]


_EDO = {
    "euler": dict(
        nombre="Euler", paso=_paso_euler, titulo_iter=False,
        cols=lambda o: ["f(xi, yi)"],
        formula=lambda o: ["yi+1 = yi + h · f(xi, yi)      (ecuación 1)"],
    ),
    "heun": dict(
        nombre="Euler mejorado", paso=_paso_heun, titulo_iter=False,
        cols=lambda o: ["f(xi, yi)", "ȳi+1", "f(xi+1, ȳi+1)"],
        formula=lambda o: ["Predictor:  ȳi+1 = yi + h · f(xi, yi)",
                           "Corrector:  yi+1 = yi + h/2 · [ f(xi, yi) + f(xi+1, ȳi+1) ]      (ecuación 2)"],
    ),
    "rk": dict(
        nombre="Runge-Kutta", paso=_paso_rk, titulo_iter=True,
        cols=lambda o: [f"k{j}" for j in range(1, len(_RK[o]["c"]) + 1)],
        formula=_formula_rk,
    ),
}


def _grafica_edo(xs, ys, exacta, x0, xf, nombre):
    capas = [dict(tipo="linea", pts=list(zip(xs, ys)), color=C["euler"], ancho=3, leyenda=nombre)]
    if len(xs) <= 200:
        capas.append(dict(tipo="puntos", pts=list(zip(xs, ys)), color=C["euler"]))
    if exacta is not None:
        capas.append(dict(tipo="linea", pts=muestrear(exacta, x0, xf, 160),
                          color=C["exacta"], ancho=2, punteado=True, leyenda="solución analítica"))
    return dict(titulo=f"Solución con {nombre}", capas=capas)


def _resolver_edo(d, clave):
    dec = d["dec"]
    F = lambda v: fmt(v, dec)
    metodo = _EDO[clave]
    c = _leer_edo(d)
    f, x0, y0, xf, n, h = c["f"], c["x0"], c["y0"], c["xf"], c["n"], c["h"]
    exacta, xq, iq = c["exacta"], c["xq"], c["iq"]
    orden = None
    if clave == "rk":
        orden = leer_entero(d["orden"], "Orden del método", 1, 1000)
        if orden not in _RK:
            raise ErrorMatematico(
                f"No se puede usar Runge-Kutta de orden {orden} con esta lógica. El PDF trae el orden 2, 3 y 4 "
                f"(y el programa añade 5 y 6). Del orden 5 en adelante hacen falta más etapas k que el orden "
                "(6 para el 5, 7 para el 6, 9 para el 7, 11 para el 8, y aún más para el 9 y el 10), con tablas "
                "de coeficientes largas que no están en el PDF."
            )
    nombre = metodo["nombre"] + (f" de orden {orden}" if orden else "")
    R = _redondeador(d, dec)

    xs = [x0 + i * h for i in range(n + 1)]
    xs[-1] = xf
    ys, infos = [y0], []
    for i in range(n):
        y_nuevo, lineas, extra = metodo["paso"](
            dict(f=f, x=xs[i], x_sig=xs[i + 1], y=ys[i], h=h, i=i, R=R, dec=dec, F=F, orden=orden))
        _vigilar(y_nuevo, i, h)
        ys.append(y_nuevo)
        infos.append((lineas, extra))

    p = Pasos()
    p.titulo("Datos del problema (PVI)")
    p.formula(f"dy/dx = f(x, y) = {bonita(d['f'], ('x', 'y'))}")
    p.formula(f"y(x0) = y({fc(x0, dec)}) = {fc(y0, dec)}          y(xf) = y({fc(xf, dec)}) = ?")
    p.texto(f"Se divide el intervalo [{fc(x0, dec)}, {fc(xf, dec)}] en n = {n} subintervalos. "
            f"Método: {nombre}." + (f" Cada y se redondea a {dec} decimales, como en las diapositivas."
                                    if d.get("redondeo") else ""))
    p.titulo("Paso 1: ancho de cada subintervalo")
    p.formula(f"h = (xf − x0) / n = ({fc(xf, dec)} − {fc(x0, dec)}) / {n} = {fc(h, dec)}")
    p.titulo("Paso 2: puntos xi = x0 + i·h")
    indices = list(range(1, n + 1)) if n <= 12 else list(range(1, 6)) + [None, n]
    for i in indices:
        if i is None:
            p.formula("   ⋮")
        else:
            p.formula(f"x{i} = x{i - 1} + h = {fc(xs[i - 1], dec)} + {fc(h, dec)} = {fc(xs[i], dec)}")
    p.titulo(f"Paso 3: fórmula de {nombre}")
    if orden and orden > 4:
        p.aviso(f"El orden {orden} no está en el PDF: usa los coeficientes de Butcher ({len(_RK[orden]['c'])} etapas).")
    for linea in metodo["formula"](orden):
        p.formula(linea)
    p.titulo("Paso 4: iteraciones")
    indices = list(range(n)) if n <= 20 else list(range(5)) + [None, n - 2, n - 1]
    for i in indices:
        if i is None:
            p.formula(f"   ⋮   (iteraciones 6 a {n - 2}: están en la pestaña «Tabla de valores»)")
            continue
        if metodo["titulo_iter"]:
            p.titulo(f"Iteración {i + 1}  (de x{i} = {fc(xs[i], dec)} a x{i + 1} = {fc(xs[i + 1], dec)})")
        for linea in infos[i][0]:
            p.formula(linea)

    ir = iq if iq is not None else n
    xr = xs[ir]
    p.titulo("Resultado")
    p.resultado(f"y({fc(xf, dec)}) ≈ {F(ys[-1])}")
    if iq is not None and iq != n:
        p.resultado(f"y({fc(xq, dec)}) ≈ {F(ys[iq])}")
    if exacta is not None:
        ex = _valor_exacto(exacta, xr)
        err = abs(ex - ys[ir])
        p.titulo("Comparación con la solución analítica")
        p.formula(f"y({fc(xr, dec)}) analítica = {F(ex)}")
        p.formula(f"Error absoluto = |{F(ex)} − {F(ys[ir])}| = {F(err)}")
        if ex != 0:
            p.formula(f"Error relativo porcentual:  ER = | ({F(ex)} − {F(ys[ir])}) / {F(ex)} | × 100 = {err / abs(ex) * 100:.2f} %")
        else:
            p.texto("El valor analítico es 0: el error relativo no está definido.")

    cols = ["i", "xi", "yi"] + metodo["cols"](orden)
    if exacta is not None:
        cols += ["y analítica", "error"]
    filas = []
    for i in range(n + 1):
        extra = infos[i][1] if i < n else ["—"] * len(metodo["cols"](orden))
        fila = [i, F(xs[i]), F(ys[i])] + list(extra)
        if exacta is not None:
            ex = _valor_exacto(exacta, xs[i])
            fila += [F(ex), F(abs(ex - ys[i]))]
        filas.append(tuple(fila))
    return Resultado(f"y en x = {fc(xr, dec)}", F(ys[ir]), p, cols, filas,
                     _grafica_edo(xs, ys, exacta, x0, xf, nombre), [])


def metodo_euler(d):
    return _resolver_edo(d, "euler")


def metodo_euler_mejorado(d):
    return _resolver_edo(d, "heun")


def metodo_runge_kutta(d):
    return _resolver_edo(d, "rk")


# ======================================================================
# 6. CATÁLOGO DE MÉTODOS
# ======================================================================
def _campo(clave, etiqueta, defecto, ayuda, modo="ambos", tipo="entry", valores=None):
    return dict(clave=clave, etiqueta=etiqueta, defecto=defecto, ayuda=ayuda,
                modo=modo, tipo=tipo, valores=valores or [])


_AYUDA_F = "Escribe la función con x. Ejemplos: x^2 + 1,  sen(x),  e^(x^2),  1/(1+x^2),  sqrt(x),  ln(x)."
_AYUDA_AB = "Puedes escribir expresiones: 2,  0.5,  pi/2,  sqrt(3)."
_AYUDA_X = "Separa los valores con espacios o comas. Los decimales van con punto: 13.4"
_AYUDA_EXACTO = "Opcional. Si conoces la respuesta exacta, el programa calcula el error de la aproximación."
_XS_PDF = "500 900 1400 1800 2000 2200"
_YS_PDF = "9.0 13.4 18.7 23.0 25.1 27.2"


def _campos_integral(n_etiqueta, n_defecto, n_ayuda, n_valores=None):
    return [
        _campo("f", "f(x)", "2+3*x", _AYUDA_F, modo="funcion"),
        _campo("a", "Límite inferior a", "0", _AYUDA_AB, modo="funcion"),
        _campo("b", "Límite superior b", "5", _AYUDA_AB, modo="funcion"),
        _campo("n", n_etiqueta, n_defecto, n_ayuda, modo="funcion",
               tipo="combo" if n_valores else "entry", valores=n_valores),
        _campo("xs", "Valores de x", _XS_PDF, _AYUDA_X, modo="tabla"),
        _campo("ys", "Valores de f(x)", _YS_PDF, _AYUDA_X, modo="tabla"),
        _campo("ta", "Desde x =", "500", "Valor de x donde empieza el área. Debe estar en la tabla (vacío = desde el primero).", modo="tabla"),
        _campo("tb", "Hasta x =", "1800", "Valor de x donde termina el área. Debe estar en la tabla (vacío = hasta el último).", modo="tabla"),
        _campo("exacto", "Valor exacto", "", _AYUDA_EXACTO),
    ]


def _ejemplos_integral(n1, n2, n3, extra_tabla=None, etiqueta_tabla="Ej. 4"):
    ej = [
        dict(nombre=f"Ejemplo 1: ∫ de 0 a 5 de (2 + 3x) dx,  n = {n1}",
             valores=dict(f="2+3*x", a="0", b="5", n=n1, exacto="47.5")),
        dict(nombre=f"Ejemplo 2: ∫ de 1 a 4 de e^(x²) dx,  n = {n2}",
             valores=dict(f="e^(x^2)", a="1", b="4", n=n2, exacto="")),
        dict(nombre=f"Ejemplo 3: ∫ de 0 a π/2 de sen x dx,  n = {n3}",
             valores=dict(f="sen(x)", a="0", b="pi/2", n=n3, exacto="1")),
        dict(nombre=f"{etiqueta_tabla}: tabla, área en [500, 1800]",
             modo="tabla",
             valores=dict(xs=_XS_PDF, ys=_YS_PDF, ta="500", tb="1800", exacto="")),
    ]
    if extra_tabla:
        ej.append(extra_tabla)
    return ej


_TABLA_EQUI = dict(
    nombre="Tabla con x igualmente espaciados (f = x² + 1, de 0 a 4)",
    modo="tabla",
    valores=dict(xs="0 1 2 3 4", ys="1 2 5 10 17", ta="0", tb="4", exacto="25.3333333333"),
)

_DESC_NC_TABLA = dict(
    nombre="Tabla con x igualmente espaciados (f = x² + 1, de 0 a 4)",
    modo="tabla",
    valores=dict(xs="0 1 2 3 4", ys="1 2 5 10 17", ta="0", tb="4", exacto="25.3333333333"),
)

METODOS = [
    dict(
        id="trapecio", vista="integral", grupo="Integración numérica", nombre="Trapecio", sub="Simple y compuesto", insignia="T",
        formula=[
            "#Simple (n = 1)",
            r"I = \frac{h}{2}\left[ f(x_0) + f(x_1) \right]",
            r"I = \frac{b-a}{2}\left[ f(x_a) + f(x_b) \right]",
            "#Compuesto (n ≥ 2)",
            r"I = \frac{h}{2}\left[ f(x_0) + 2\sum_{i=1}^{n-1} f(x_i) + f(x_n) \right]",
        ],
        descripcion=("Aproxima f con rectas (polinomio de grado 1) y suma el área de los trapecios. "
                     "Funciona con cualquier n ≥ 1 y, con datos de una tabla, incluso si los x no están "
                     "igualmente espaciados."),
        tabla=True, funcion=metodo_trapecio,
        campos=_campos_integral("Subintervalos n", "6", "Cantidad de trapecios. Con n = 1 es el trapecio simple; con n ≥ 2, el compuesto."),
        ejemplos=_ejemplos_integral("1", "6", "6", etiqueta_tabla="Ejemplo 4"),
    ),
    dict(
        id="simpson13", vista="integral", grupo="Integración numérica", nombre="Simpson 1/3", sub="Simple y compuesto", insignia="1/3",
        formula=[
            "#Simple (n = 2)",
            r"I = \frac{h}{3}\left[ f(x_0) + 4f(x_1) + f(x_2) \right]",
            "#Compuesto (n par)",
            r"I = \frac{h}{3}\left[ f(x_0) + 4\sum_{\substack{i=1\\ \Delta i=2}}^{n-1} f(x_i) \right.",
            r"\qquad\left. + 2\sum_{\substack{i=2\\ \Delta i=2}}^{n-2} f(x_i) + f(x_n) \right]",
        ],
        descripcion=("Aproxima f con parábolas (polinomio de grado 2) tomando los puntos de a tres. "
                     "Necesita un número PAR de subintervalos y un paso h constante."),
        tabla=True, funcion=metodo_simpson13,
        campos=_campos_integral("Subintervalos n", "4", "Debe ser PAR: 2, 4, 6, … (con n = 2 es el Simpson 1/3 simple)."),
        ejemplos=_ejemplos_integral("2", "6", "4", etiqueta_tabla="Ejemplo 8", extra_tabla=_TABLA_EQUI),
    ),
    dict(
        id="simpson38", vista="integral", grupo="Integración numérica", nombre="Simpson 3/8", sub="Simple y compuesto", insignia="3/8",
        formula=[
            "#Simple (n = 3)",
            r"I = \frac{3h}{8}\left[ f(x_0) + 3f(x_1) + 3f(x_2) + f(x_3) \right]",
            "#Compuesto (n múltiplo de 3)",
            r"I = \frac{3h}{8}\left[ f(x_0) + 3\sum_{\substack{i=1\\ \Delta i=3}}^{n-2} f(x_i) \right.",
            r"\qquad\left. + 3\sum_{\substack{i=2\\ \Delta i=3}}^{n-1} f(x_i) + 2\sum_{\substack{i=3\\ \Delta i=3}}^{n-3} f(x_i) + f(x_n) \right]",
        ],
        descripcion=("Aproxima f con polinomios de grado 3, tomando los puntos de a cuatro. "
                     "Necesita que n sea múltiplo de 3 y un paso h constante."),
        tabla=True, funcion=metodo_simpson38,
        campos=_campos_integral("Subintervalos n", "6", "Debe ser múltiplo de 3: 3, 6, 9, … (con n = 3 es el Simpson 3/8 simple)."),
        ejemplos=_ejemplos_integral("3", "6", "6", etiqueta_tabla="Ejemplo 12"),
    ),
    dict(
        id="newton", vista="integral", grupo="Integración numérica", nombre="Newton-Cotes", sub="n = 4, 5 y 6", insignia="NC",
        formula=[
            "#n = 4",
            r"I = \frac{2h}{45}\left[ 7f(x_0) + 32f(x_1) + 12f(x_2) + 32f(x_3) + 7f(x_4) \right]",
            "#n = 5",
            r"I = \frac{5h}{288}\left[ 19f(x_0) + 75f(x_1) + 50f(x_2) \right.",
            r"\qquad\left. + 50f(x_3) + 75f(x_4) + 19f(x_5) \right]",
            "#n = 6",
            r"I = \frac{h}{140}\left[ 41f(x_0) + 216f(x_1) + 27f(x_2) + 272f(x_3) \right.",
            r"\qquad\left. + 27f(x_4) + 216f(x_5) + 41f(x_6) \right]",
        ],
        descripcion=("Fórmulas cerradas de Newton-Cotes de orden superior que aparecen junto a Simpson 3/8 "
                     "en el PDF. Se aplican una sola vez sobre todo el intervalo."),
        tabla=True, funcion=metodo_newton_cotes,
        campos=_campos_integral("Subintervalos n", "4", "El PDF trae las fórmulas para n = 4, 5 y 6.", n_valores=["4", "5", "6"]),
        ejemplos=[
            dict(nombre="∫ de 0 a 5 de (2 + 3x) dx,  n = 4",
                 valores=dict(f="2+3*x", a="0", b="5", n="4", exacto="47.5")),
            dict(nombre="∫ de 0 a π/2 de sen x dx,  n = 6",
                 valores=dict(f="sen(x)", a="0", b="pi/2", n="6", exacto="1")),
            dict(nombre="∫ de 1 a 4 de e^(x²) dx,  n = 5",
                 valores=dict(f="e^(x^2)", a="1", b="4", n="5", exacto="")),
            _DESC_NC_TABLA,
        ],
    ),
    dict(
        id="gauss", vista="gauss", grupo="Integración numérica", nombre="Cuadratura Gaussiana", sub="2 a 10 puntos", insignia="∫",
        formula=[
            r"\int_a^b f(x)\,dx \approx \frac{b-a}{2}\sum_{i=1}^{n} W_i\,f(x_i)",
            r"x_i = \frac{(b-a)\,t_i + (a+b)}{2}",
            "#Los nodos t y los pesos W vienen de la Tabla 1 (intervalo [−1, 1])",
        ],
        descripcion=("No usa un paso fijo: elige nodos ti y pesos Wi especiales en [−1, 1] y cambia de "
                     "variable para cualquier intervalo [a, b]. Con n puntos es exacta para polinomios "
                     "de grado hasta 2n − 1. El programa admite de 2 a 10 puntos (la Tabla 1 del PDF llega a 4)."),
        tabla=False, funcion=metodo_gauss,
        campos=[
            _campo("f", "f(x)", "e^(-x^2)", _AYUDA_F),
            _campo("a", "Límite inferior a", "1", _AYUDA_AB),
            _campo("b", "Límite superior b", "1.5", _AYUDA_AB),
            _campo("npuntos", "Número de puntos n", "2",
                   "La Tabla 1 del PDF trae 2, 3 y 4 puntos; de 5 a 10 los nodos se calculan (raíces del polinomio de Legendre).",
                   tipo="combo", valores=[str(k) for k in range(2, 11)]),
            _campo("precision", "Nodos y pesos", _PRECISION[0],
                   "«Como la Tabla 1 del PDF»: los números tal como están impresos (2 a 4 puntos). «Exactos»: todos los "
                   "decimales. «Cortados»: 4 decimales (0.5773).", tipo="combo", valores=_PRECISION),
            _campo("exacto", "Valor exacto", "sqrt(pi)/2*(erf(1.5)-erf(1))", _AYUDA_EXACTO + " Puedes usar erf(x)."),
        ],
        ejemplos=[
            dict(nombre="Ejemplo 5: ∫ de 1 a 1.5 de e^(−x²) dx,  2 puntos",
                 valores=dict(f="e^(-x^2)", a="1", b="1.5", npuntos="2", precision=_PRECISION[0],
                              exacto="sqrt(pi)/2*(erf(1.5)-erf(1))")),
            dict(nombre="Ejemplo 6: densidad normal en (−0.8, 1.5),  2 puntos",
                 valores=dict(f="1/sqrt(2*pi)*e^(-x^2/2)", a="-0.8", b="1.5", npuntos="2", precision=_PRECISION[0],
                              exacto="(erf(1.5/sqrt(2))-erf(-0.8/sqrt(2)))/2")),
            dict(nombre="Ejemplo 6 con 3 puntos",
                 valores=dict(f="1/sqrt(2*pi)*e^(-x^2/2)", a="-0.8", b="1.5", npuntos="3", precision=_PRECISION[0],
                              exacto="(erf(1.5/sqrt(2))-erf(-0.8/sqrt(2)))/2")),
            dict(nombre="Ejemplo 6 con 4 puntos",
                 valores=dict(f="1/sqrt(2*pi)*e^(-x^2/2)", a="-0.8", b="1.5", npuntos="4", precision=_PRECISION[0],
                              exacto="(erf(1.5/sqrt(2))-erf(-0.8/sqrt(2)))/2")),
        ],
    ),
]


def _campos_edo(f, y0, n, xq, exacta, con_orden=False):
    campos = [
        _campo("f", "dy/dx = f(x, y)", f, "Escribe f con x e y. Ejemplos: 2xy,  x - y,  x + y,  sen(x) - y."),
        _campo("x0", "x inicial  x0", "0", _AYUDA_AB),
        _campo("y0", "Condición inicial  y(x0) =", y0, "Valor de y en x0."),
        _campo("xf", "x final  xf", "1", "Valor de x donde se quiere conocer y(xf). Debe ser mayor que x0."),
        _campo("n", "Subintervalos  n", n, "Cantidad de pasos (iteraciones). El ancho de cada uno es h = (xf − x0)/n."),
    ]
    if con_orden:
        campos.append(_campo("orden", "Orden del método", "4",
                             "El PDF trae Runge-Kutta de orden 2, 3 y 4. Los órdenes 5 y 6 son un extra (no están en el PDF).",
                             tipo="combo", valores=["2", "3", "4", "5", "6"]))
    campos += [
        _campo("xq", "Aproximar y en x =", xq,
               "Opcional, como en «Aproxime y(0.5)». Debe ser uno de los puntos xi = x0 + i·h."),
        _campo("exacta", "Solución analítica y(x)", exacta,
               "Opcional. Si la conoces (Ejemplo 1: e^(x^2)) se grafica y se calcula el error relativo porcentual."),
        _campo("redondeo", "Redondear cada y a los decimales de abajo", False,
               "Las diapositivas calculan a mano y redondean (Ejemplo 2: 2 decimales). Actívalo y pon los mismos "
               "decimales para reproducir sus valores.", tipo="check"),
    ]
    return campos


_EJ1 = dict(f="2*x*y", x0="0", y0="1", xf="1", n="10", xq="0.5", exacta="e^(x^2)", redondeo=False)
_EJ23 = dict(f="x - y", x0="0", y0="2", xf="1", n="5", xq="", exacta="", redondeo=False)

_FORMULA_RK = {
    "2": [
        "#Orden 2 (ecuación 3)",
        r"y_{i+1} = y_i + \frac{h}{2}\,(k_1 + k_2)",
        r"k_1 = f(x_i, y_i)",
        r"k_2 = f(x_i + h,\; y_i + k_1 h)",
    ],
    "3": [
        "#Orden 3 (ecuación 4)",
        r"y_{i+1} = y_i + \frac{h}{6}\,(k_1 + 4k_2 + k_3)",
        r"k_1 = f(x_i, y_i)",
        r"k_2 = f\left(x_i + \frac{1}{2}h,\; y_i + \frac{1}{2}k_1 h\right)",
        r"k_3 = f(x_i + h,\; y_i - k_1 h + 2k_2 h)",
    ],
    "4": [
        "#Orden 4 (ecuación 5)",
        r"y_{i+1} = y_i + \frac{h}{6}\,(k_1 + 2k_2 + 2k_3 + k_4)",
        r"k_1 = f(x_i, y_i)",
        r"k_2 = f\left(x_i + \frac{1}{2}h,\; y_i + \frac{1}{2}k_1 h\right)",
        r"k_3 = f\left(x_i + \frac{1}{2}h,\; y_i + \frac{1}{2}k_2 h\right)",
        r"k_4 = f(x_i + h,\; y_i + k_3 h)",
    ],
    "5": [
        "#Orden 5 (extra: no está en el PDF; coeficientes de Butcher)",
        r"y_{i+1} = y_i + \frac{h}{90}\,(7k_1 + 32k_3 + 12k_4 + 32k_5 + 7k_6)",
        r"k_1 = f(x_i, y_i)",
        r"k_2 = f\left(x_i + \frac{h}{4},\; y_i + \frac{h}{4}k_1\right)",
        r"k_3 = f\left(x_i + \frac{h}{4},\; y_i + \frac{h}{8}(k_1 + k_2)\right)",
        r"k_4 = f\left(x_i + \frac{h}{2},\; y_i - \frac{h}{2}k_2 + h k_3\right)",
        r"k_5 = f\left(x_i + \frac{3h}{4},\; y_i + \frac{h}{16}(3k_1 + 9k_4)\right)",
        r"k_6 = f\left(x_i + h,\; y_i + \frac{h}{7}(-3k_1 + 2k_2 + 12k_3 - 12k_4 + 8k_5)\right)",
    ],
    "6": [
        "#Orden 6 (extra: no está en el PDF; coeficientes de Butcher)",
        r"y_{i+1} = y_i + \frac{h}{120}\,(11k_1 + 81k_3 + 81k_4 - 32k_5 - 32k_6 + 11k_7)",
        r"k_1 = f(x_i, y_i)",
        r"k_2 = f\left(x_i + \frac{h}{3},\; y_i + \frac{h}{3}k_1\right)",
        r"k_3 = f\left(x_i + \frac{2h}{3},\; y_i + \frac{2h}{3}k_2\right)",
        r"k_4 = f\left(x_i + \frac{h}{3},\; y_i + \frac{h}{12}(k_1 + 4k_2 - k_3)\right)",
        r"k_5 = f\left(x_i + \frac{h}{2},\; y_i + \frac{h}{16}(-k_1 + 18k_2 - 3k_3 - 6k_4)\right)",
        r"k_6 = f\left(x_i + \frac{h}{2},\; y_i + \frac{h}{8}(9k_2 - 3k_3 - 6k_4 + 4k_5)\right)",
        r"k_7 = f\left(x_i + h,\; y_i + \frac{h}{44}(9k_1 - 36k_2 + 63k_3 + 72k_4 - 64k_6)\right)",
    ],
}

_METODOS_EDO = [
    dict(
        id="euler", vista="edo", grupo="Ecuaciones diferenciales", nombre="Euler", sub="Método de las tangentes", insignia="E",
        formula=[
            r"h = \frac{x_f - x_0}{n}, \qquad x_i = x_0 + i\,h",
            r"y_{i+1} = y_i + h\,f(x_i, y_i)",
            "#Ecuación (1) del PDF",
        ],
        descripcion=("También llamado método de las tangentes: parte de (x0, y0) y avanza por la recta de "
                     "pendiente f(x, y) en pasos de ancho h, aproximando la curva solución con segmentos de recta."),
        tabla=False, funcion=metodo_euler,
        campos=_campos_edo(_EJ1["f"], _EJ1["y0"], _EJ1["n"], _EJ1["xq"], _EJ1["exacta"]),
        ejemplos=[
            dict(nombre="Ejemplo 1: dy/dx = 2xy, y(0) = 1, [0, 1], n = 10, aproximar y(0.5)",
                 valores=dict(_EJ1), decimales="8"),
            dict(nombre="Ejemplo 2: dy/dx = x − y, y(0) = 2, [0, 1], n = 5 (con Euler)",
                 valores=dict(_EJ23), decimales="6"),
        ],
    ),
    dict(
        id="euler_mejorado", vista="edo", grupo="Ecuaciones diferenciales", nombre="Euler mejorado", sub="Método de Heun", insignia="E+",
        formula=[
            "#Predictor",
            r"\bar{y}_{i+1} = y_i + h\,f(x_i, y_i)",
            "#Corrector (ecuación 2)",
            r"y_{i+1} = y_i + \frac{h}{2}\left[ f(x_i, y_i) + f(x_{i+1}, \bar{y}_{i+1}) \right]",
        ],
        descripcion=("También llamado método de Heun: usa el promedio de la derivada en los dos extremos del "
                     "intervalo. Primero predice ȳ con Euler y luego corrige con ese promedio."),
        tabla=False, funcion=metodo_euler_mejorado,
        campos=_campos_edo(_EJ23["f"], _EJ23["y0"], _EJ23["n"], _EJ23["xq"], _EJ23["exacta"]),
        ejemplos=[
            dict(nombre="Ejemplo 2: dy/dx = x − y, y(0) = 2, [0, 1], n = 5 (redondeando a 2 decimales como la diapositiva)",
                 valores=dict(_EJ23, redondeo=True), decimales="2"),
            dict(nombre="Ejemplo 2 sin redondear los pasos",
                 valores=dict(_EJ23), decimales="6"),
            dict(nombre="Ejemplo 1 del PDF (2xy) resuelto con Euler mejorado",
                 valores=dict(_EJ1), decimales="8"),
        ],
    ),
    dict(
        id="rk", vista="edo", grupo="Ecuaciones diferenciales", nombre="Runge-Kutta", sub="Orden 2 a 6", insignia="RK",
        formula=_FORMULA_RK["4"], formula_por=("orden", _FORMULA_RK),
        descripcion=("Logra la exactitud de la serie de Taylor sin calcular derivadas de orden superior. "
                     "El de orden 2 es el Euler mejorado en un solo paso; el de orden 4 es el más popular. "
                     "(Los órdenes 5 y 6 son un extra: no están en el PDF.)"),
        tabla=False, funcion=metodo_runge_kutta,
        campos=_campos_edo(_EJ23["f"], _EJ23["y0"], _EJ23["n"], _EJ23["xq"], _EJ23["exacta"], con_orden=True),
        ejemplos=[
            dict(nombre="Ejemplo 3: dy/dx = x − y, y(0) = 2, [0, 1], n = 5, orden 4",
                 valores=dict(_EJ23, orden="4"), decimales="9"),
            dict(nombre="Ejemplo 3 con orden 3",
                 valores=dict(_EJ23, orden="3"), decimales="6"),
            dict(nombre="Ejemplo 3 con orden 2 (equivale al Euler mejorado)",
                 valores=dict(_EJ23, orden="2"), decimales="6"),
            dict(nombre="Ejemplo 1 del PDF (2xy) resuelto con Runge-Kutta de orden 4",
                 valores=dict(_EJ1, orden="4"), decimales="8"),
        ],
    ),
]

METODOS.extend(_METODOS_EDO)


# ======================================================================
# MOTOR INTELIGENTE / RECOMENDADOR DE MÉTODOS (OFFLINE + ONLINE IA)
# ======================================================================
def analizar_problema_heuristico(texto):
    """
    Analizador experto offline sin necesidad de conexión ni API key.
    Inspecciona el enunciado, detecta si es EDO o Integración, si hay tablas,
    número de subintervalos, espaciado de paso, orden requerido, etc.
    """
    t = texto.strip()
    t_min = t.lower()

    # --- 1. Detección de EDO (Ecuaciones Diferenciales Ordinarias) ---
    es_edo = any(w in t_min for w in [
        "dy/dx", "y'", "dy / dx", "diferencial", "pvi", "euler", "runge", "kutta",
        "y(0)", "y(", "condicion inicial", "condición inicial", "valor inicial"
    ])

    if es_edo:
        f_val = "2*x*y"
        m_f = re.search(r"(?:dy/dx|y'|f\(x,?\s*y\))\s*=\s*([^,\n;]+)", t, re.I)
        if m_f:
            f_val = m_f.group(1).strip()
        elif "x - y" in t_min:
            f_val = "x - y"
        elif "2xy" in t_min:
            f_val = "2*x*y"

        x0_val, y0_val = "0", "1"
        m_ci = re.search(r"y\s*\(\s*([0-9.]+)\s*\)\s*=\s*([0-9.-]+)", t)
        if m_ci:
            x0_val, y0_val = m_ci.group(1), m_ci.group(2)

        xf_val = "1"
        m_xf = re.search(r"(?:hasta\s*x\s*=|en\s*x\s*=|y\s*\(\s*)([0-9.]+)(?:\s*\)|(?:\s*donde|\s*con|\s*\.|\s*,|\s*$))", t)
        if m_xf and m_xf.group(1) != x0_val:
            xf_val = m_xf.group(1)

        n_val = "5"
        m_n = re.search(r"\b(?:n\s*=\s*|subintervalos?\s*[:=]?\s*|pasos?\s*[:=]?\s*)([0-9]+)\b", t, re.I)
        if m_n:
            n_val = m_n.group(1)
        else:
            m_h = re.search(r"\bh\s*=\s*([0-9.]+)\b", t, re.I)
            if m_h:
                try:
                    h_flt = float(m_h.group(1))
                    if h_flt > 0:
                        n_calc = int(round((float(xf_val) - float(x0_val)) / h_flt))
                        if n_calc > 0:
                            n_val = str(n_calc)
                except Exception:
                    pass

        if "euler mejorado" in t_min or "heun" in t_min:
            mid = "euler_mejorado"
            nombre = "Euler Mejorado (Método de Heun)"
            just = ("El problema pide aproximar la solución de una EDO (PVI) mediante el método de Heun / Euler Mejorado. "
                    "Este método de 2º orden predice un valor tentativo y lo corrige con el promedio de las derivadas en los extremos.")
            orden_info = "Orden 2 (Error local de truncamiento O(h³), global O(h²))."
            valores = dict(f=f_val, x0=x0_val, y0=y0_val, xf=xf_val, n=n_val, xq="", exacta="", redondeo=False)
        elif "euler" in t_min and "runge" not in t_min and "kutta" not in t_min:
            mid = "euler"
            nombre = "Euler (Método de las tangentes)"
            just = ("El ejercicio plantea un Problema de Valor Inicial (PVI) dy/dx = f(x, y). "
                    "Se aplica el método de Euler de primer orden avanzando a lo largo de la recta tangente.")
            orden_info = "Orden 1 (Error local O(h²), global O(h))."
            valores = dict(f=f_val, x0=x0_val, y0=y0_val, xf=xf_val, n=n_val, xq="", exacta="", redondeo=False)
        else:
            mid = "rk"
            orden = "4"
            m_ord = re.search(r"(?:orden|rk)\s*([2-6])", t, re.I)
            if m_ord:
                orden = m_ord.group(1)
            nombre = f"Runge-Kutta de Orden {orden}"
            just = (f"Se trata de una EDO con condición inicial. Runge-Kutta de orden {orden} ofrece gran precisión "
                    "evaluando múltiples pendientes k por paso sin necesidad de calcular derivadas analíticas superiores.")
            orden_info = f"Orden {orden} (con {orden} evaluaciones de pendiente k por paso)."
            valores = dict(f=f_val, x0=x0_val, y0=y0_val, xf=xf_val, n=n_val, orden=orden, xq="", exacta="", redondeo=False)

        casillas = [
            ("f (o dy/dx)", f_val, "Expresión matemática de la derivada dy/dx"),
            ("x0 (x inicial)", x0_val, "Punto donde se conoce la condición inicial"),
            ("y0 (y inicial)", y0_val, "Valor inicial de y(x0)"),
            ("xf (x final)", xf_val, "Punto donde se busca aproximar el resultado"),
            ("n (subintervalos)", n_val, "Número de pasos para dividir [x0, xf]"),
        ]
        return dict(metodo_id=mid, nombre=nombre, modo="funcion", justificacion=just,
                    orden_info=orden_info, casillas=casillas, valores=valores)

    # --- 2. Detección de Datos Tabulados ---
    lineas = [ln.strip() for ln in t.splitlines() if ln.strip()]
    numeros = []
    for ln in lineas:
        nums = re.findall(r"[-+]?(?:\d*\.\d+|\d+)", ln)
        if len(nums) >= 2:
            numeros.append([float(x) for x in nums])

    hay_tabla = False
    xs_rec, ys_rec = [], []
    if len(numeros) >= 2 and len(numeros[0]) == len(numeros[1]) and len(numeros[0]) >= 2:
        xs_rec = [g(v) for v in numeros[0]]
        ys_rec = [g(v) for v in numeros[1]]
        hay_tabla = True
    else:
        m_x = re.search(r"(?:usuarios|x|tiempo|t)\s*[:=]\s*([0-9.,\s]+)", t, re.I)
        m_y = re.search(r"(?:instruccion|instrucciones|tiempo|y|f\(x\)|velocidad)\s*[:=]\s*([0-9.,\s]+)", t, re.I)
        if m_x and m_y:
            x_raw = re.findall(r"[-+]?(?:\d*\.\d+|\d+)", m_x.group(1))
            y_raw = re.findall(r"[-+]?(?:\d*\.\d+|\d+)", m_y.group(1))
            if len(x_raw) == len(y_raw) and len(x_raw) >= 2:
                xs_rec, ys_rec = x_raw, y_raw
                hay_tabla = True

    if hay_tabla:
        n_sub = len(xs_rec) - 1
        xs_flt = [float(x) for x in xs_rec]
        pasos = [xs_flt[i + 1] - xs_flt[i] for i in range(n_sub)]
        equi = _es_constante(pasos)

        if not equi:
            mid = "trapecio"
            nombre = "Trapecio Compuesto (Datos Tabulados con espaciado irregular)"
            just = (f"Tienes una tabla con {len(xs_rec)} puntos ({n_sub} subintervalos). Los anchos de paso entre "
                    f"puntos NO son iguales (varían entre {min(pasos):.4g} y {max(pasos):.4g}). Simpson y Newton-Cotes "
                    "exigen paso h constante, por lo que el ÚNICO método aplicable aquí es el Trapecio.")
            orden_info = "Orden 1 (Aproximación lineal por segmentos)."
        elif n_sub % 2 == 0 and n_sub >= 2:
            mid = "simpson13"
            nombre = "Simpson 1/3 Compuesto"
            just = (f"Los datos están igualmente espaciados (paso constante h = {pasos[0]:.4g}) y la cantidad de "
                    f"subintervalos n = {n_sub} es PAR. Simpson 1/3 aproxima los datos mediante arcos de parábola "
                    "con mayor precisión que el trapecio.")
            orden_info = "Orden 2 (Aproximación parabólica, exacta para polinomios hasta grado 3)."
        elif n_sub % 3 == 0 and n_sub >= 3:
            mid = "simpson38"
            nombre = "Simpson 3/8 Compuesto"
            just = (f"Los datos tienen paso constante h = {pasos[0]:.4g} y n = {n_sub} es múltiplo de 3. "
                    "Simpson 3/8 aproxima cada bloque de 3 subintervalos mediante un polinomio cúbico.")
            orden_info = "Orden 3 (Aproximación cúbica)."
        else:
            mid = "trapecio"
            nombre = "Trapecio Compuesto"
            just = (f"Datos tabulados con n = {n_sub} subintervalos. Al no ser n par ni múltiplo de 3, "
                    "el método estándar directo y seguro es el Trapecio compuesto.")
            orden_info = "Orden 1."

        valores = dict(xs=" ".join(xs_rec), ys=" ".join(ys_rec), ta=xs_rec[0], tb=xs_rec[-1], exacto="")
        casillas = [
            ("Valores de x", " ".join(xs_rec), "Lista de valores x separados por espacio"),
            ("Valores de f(x)", " ".join(ys_rec), "Valores correspondientes medidos o tabulados"),
            ("Desde x =", xs_rec[0], "Límite inferior para calcular el área acumulada"),
            ("Hasta x =", xs_rec[-1], "Límite superior"),
        ]
        return dict(metodo_id=mid, nombre=nombre, modo="tabla", justificacion=just,
                    orden_info=orden_info, casillas=casillas, valores=valores)

    # --- 3. Detección de Integrales con función continua f(x) ---
    f_val = "2+3*x"
    m_fn = re.search(r"(?:∫|integral|f\(x\)\s*=)\s*([^,;=\ndx]+)", t, re.I)
    if m_fn:
        f_val = m_fn.group(1).strip()
    elif "e^(-x^2)" in t_min or "e^(x^2)" in t_min or "exp" in t_min:
        f_val = "e^(-x^2)"
    elif "sen" in t_min or "sin" in t_min:
        f_val = "sen(x)"

    a_val, b_val = "0", "1"
    m_lim = re.search(r"(?:de|entre|desde)\s*([0-9.a-z/]+)\s*(?:a|hasta)\s*([0-9.a-z/]+)", t, re.I)
    if m_lim:
        a_val, b_val = m_lim.group(1), m_lim.group(2)
    else:
        m_int = re.search(r"\[\s*([0-9.-]+)\s*,\s*([0-9.-]+)\s*\]", t)
        if m_int:
            a_val, b_val = m_int.group(1), m_int.group(2)

    n_val = "4"
    m_n = re.search(r"\b(?:n\s*=\s*|subintervalos?\s*[:=]?\s*)([0-9]+)\b", t, re.I)
    if m_n:
        n_val = m_n.group(1)

    n_int = int(n_val) if n_val.isdigit() else 4

    if "gauss" in t_min or "cuadratura" in t_min:
        mid = "gauss"
        nombre = "Cuadratura Gaussiana"
        just = ("El problema solicita calcular una integral definida optimizando la posición de los nodos y sus pesos. "
                "Con n puntos de Gauss se logra exactitud total para cualquier polinomio de grado 2n - 1.")
        orden_info = f"Regla de {n_val} puntos (Grado de exactitud {2 * n_int - 1})."
        valores = dict(f=f_val, a=a_val, b=b_val, npuntos=n_val, precision=_PRECISION[0], exacto="")
        casillas = [
            ("f(x)", f_val, "Función integrando continua"),
            ("Límite inferior a", a_val, "Inicio del intervalo de integración"),
            ("Límite superior b", b_val, "Final del intervalo de integración"),
            ("Número de puntos n", n_val, "Cantidad de nodos de Gauss en [-1, 1]"),
        ]
        return dict(metodo_id=mid, nombre=nombre, modo="funcion", justificacion=just,
                    orden_info=orden_info, casillas=casillas, valores=valores)

    if n_int % 2 == 0 and ("simpson" in t_min or "1/3" in t_min or "trapecio" not in t_min):
        mid = "simpson13"
        nombre = f"Simpson 1/3 {'Compuesto' if n_int > 2 else 'Simple'}"
        just = (f"Para la integral de {f_val} con n = {n_int} (que es número PAR), Simpson 1/3 ofrece un excelente "
                "balance de precisión ajustando parábolas en parejas de subintervalos.")
        orden_info = "Orden 2 (Error proporcional a h⁴)."
        valores = dict(f=f_val, a=a_val, b=b_val, n=n_val, exacto="")
        casillas = [
            ("f(x)", f_val, "Función integrando"),
            ("Límite inferior a", a_val, "Límite inferior"),
            ("Límite superior b", b_val, "Límite superior"),
            ("Subintervalos n", n_val, f"Número de subintervalos (PAR: {n_val})"),
        ]
        return dict(metodo_id=mid, nombre=nombre, modo="funcion", justificacion=just,
                    orden_info=orden_info, casillas=casillas, valores=valores)

    if n_int % 3 == 0 and ("3/8" in t_min or "simpson" in t_min):
        mid = "simpson38"
        nombre = f"Simpson 3/8 {'Compuesto' if n_int > 3 else 'Simple'}"
        just = (f"Para n = {n_int} (múltiplo de 3), la fórmula de Simpson 3/8 conecta los puntos de 4 en 4 "
                "con polinomios cúbicos.")
        orden_info = "Orden 3 (Error proporcional a h⁴)."
        valores = dict(f=f_val, a=a_val, b=b_val, n=n_val, exacto="")
        casillas = [
            ("f(x)", f_val, "Función integrando"),
            ("Límite inferior a", a_val, "Límite inferior"),
            ("Límite superior b", b_val, "Límite superior"),
            ("Subintervalos n", n_val, f"Número de subintervalos (múltiplo de 3: {n_val})"),
        ]
        return dict(metodo_id=mid, nombre=nombre, modo="funcion", justificacion=just,
                    orden_info=orden_info, casillas=casillas, valores=valores)

    mid = "trapecio"
    nombre = f"Trapecio {'Compuesto' if n_int > 1 else 'Simple'}"
    just = (f"Se evalúa la integral con n = {n_int} subintervalos. El método del Trapecio es el más intuitivo "
            "y universal, aproximando la curva mediante segmentos rectilíneos.")
    orden_info = "Orden 1 (Error proporcional a h²)."
    valores = dict(f=f_val, a=a_val, b=b_val, n=n_val, exacto="")
    casillas = [
        ("f(x)", f_val, "Función integrando"),
        ("Límite inferior a", a_val, "Límite inferior"),
        ("Límite superior b", b_val, "Límite superior"),
        ("Subintervalos n", n_val, "Número de trapecios a sumar"),
    ]
    return dict(metodo_id=mid, nombre=nombre, modo="funcion", justificacion=just,
                orden_info=orden_info, casillas=casillas, valores=valores)


def _crear_contexto_ssl():
    """Crea un contexto SSL seguro o relajado según compatibilidad del sistema."""
    try:
        return ssl.create_default_context()
    except Exception:
        pass
    try:
        return ssl._create_unverified_context()
    except Exception:
        return None


def _obtener_modelos_activos_gemini(key):
    """
    Consulta dinámicamente a la API de Google cuáles modelos exactos están activos
    y autorizados para la clave del usuario, eliminando de raíz cualquier error 404.
    Devuelve tuplas (nombre_modelo, api_version).
    """
    candidatos_por_defecto = [
        ("gemini-2.5-flash", "v1beta"),
        ("gemini-2.0-flash", "v1beta"),
        ("gemini-1.5-flash", "v1beta"),
        ("gemini-2.5-flash", "v1"),
        ("gemini-2.0-flash", "v1"),
        ("gemini-1.5-flash", "v1"),
        ("gemini-3.8-flash", "v1beta"),
        ("gemini-3.5-flash-lite", "v1beta"),
    ]

    for api_ver in ("v1beta", "v1"):
        for ctx in (_crear_contexto_ssl(), None):
            try:
                url = f"https://generativelanguage.googleapis.com/{api_ver}/models?key={key}"
                req = urllib.request.Request(
                    url,
                    headers={"x-goog-api-key": key, "User-Agent": "Antigravity/1.0"},
                    method="GET"
                )
                kwargs = {"timeout": 6}
                if ctx is not None:
                    kwargs["context"] = ctx
                with urllib.request.urlopen(req, **kwargs) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    activos = []
                    for m in data.get("models", []):
                        nom = m.get("name", "").replace("models/", "")
                        metodos = m.get("supportedGenerationMethods", [])
                        if "generateContent" in metodos and not any(x in nom for x in ("tts", "image", "embedding", "realtime", "aqa", "bison")):
                            activos.append((nom, api_ver))
                    if activos:
                        flashes = [x for x in activos if "flash" in x[0]]
                        otros = [x for x in activos if "flash" not in x[0]]
                        return flashes + otros
            except Exception:
                continue

    return candidatos_por_defecto


def consultar_api_gemini(api_key, texto_problema):
    """
    Consulta la API gratuita de Google Gemini para clasificar el ejercicio y extraer
    las casillas exactas. Detecta automáticamente los modelos disponibles para la clave.
    """
    key = api_key.strip()
    modelos_versiones = _obtener_modelos_activos_gemini(key)

    system_instruction = (
        "Eres un tutor experto en Métodos Numéricos. Tu tarea es analizar un ejercicio o problema "
        "y determinar con EXACTITUD cuál de los siguientes métodos de la aplicación debe usarse:\n"
        "- trapecio: Regla del Trapecio simple (n=1) o compuesto (n>=2), o con datos tabulados (incluso con espaciado irregular).\n"
        "- simpson13: Simpson 1/3 simple (n=2) o compuesto (n PAR: 4, 6, 8...). Requiere espaciado constante.\n"
        "- simpson38: Simpson 3/8 simple (n=3) o compuesto (n múltiplo de 3: 6, 9...). Requiere espaciado constante.\n"
        "- newton: Newton-Cotes cerrado para n=4, 5 o 6.\n"
        "- gauss: Cuadratura Gaussiana (2 a 10 puntos).\n"
        "- euler: Método de Euler para EDO dy/dx = f(x, y).\n"
        "- euler_mejorado: Método de Heun para EDO.\n"
        "- rk: Runge-Kutta (órdenes 2, 3, 4, 5 o 6) para EDO.\n\n"
        "Debes responder ÚNICAMENTE un objeto JSON válido con este formato:\n"
        "{\n"
        '  "metodo_id": "trapecio" | "simpson13" | "simpson38" | "newton" | "gauss" | "euler" | "euler_mejorado" | "rk",\n'
        '  "nombre": "Nombre descriptivo del método",\n'
        '  "modo": "funcion" | "tabla",\n'
        '  "justificacion": "Por qué este método específico es el correcto para este ejercicio según sus condiciones",\n'
        '  "orden_info": "De qué orden es el método o su precisión",\n'
        '  "casillas": [\n'
        '     {"campo": "Nombre del cuadro", "valor": "valor numérico o expresión", "motivo": "explicación"}\n'
        "  ],\n"
        '  "valores": {\n'
        '     "f": "...", "a": "...", "b": "...", "n": "...", "xs": "...", "ys": "...", "x0": "...", "y0": "...", "xf": "...", "orden": "..."\n'
        "  }\n"
        "}"
    )

    payload = {
        "contents": [
            {
                "parts": [
                    {"text": f"{system_instruction}\n\nEnunciado del ejercicio:\n{texto_problema}"}
                ]
            }
        ],
        "generationConfig": {
            "temperature": 0.1
        }
    }

    ultimo_error = None
    for modelo, api_ver in modelos_versiones:
        url = f"https://generativelanguage.googleapis.com/{api_ver}/models/{modelo}:generateContent?key={key}"
        for ctx in (_crear_contexto_ssl(), None):
            try:
                req = urllib.request.Request(
                    url,
                    data=json.dumps(payload).encode("utf-8"),
                    headers={
                        "Content-Type": "application/json",
                        "x-goog-api-key": key,
                        "User-Agent": "Antigravity/1.0",
                    },
                    method="POST"
                )
                kwargs = {"timeout": 15}
                if ctx is not None:
                    kwargs["context"] = ctx
                with urllib.request.urlopen(req, **kwargs) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    candidate = data.get("candidates", [{}])[0]
                    parts = candidate.get("content", {}).get("parts", [])
                    text_parts = [p.get("text", "") for p in parts if isinstance(p, dict) and not p.get("thought") and p.get("text")]
                    if not text_parts:
                        text_parts = [p.get("text", "") for p in parts if isinstance(p, dict) and p.get("text")]
                    texto_resp = "\n".join(text_parts).strip()

                    m_json = re.search(r"\{[\s\S]*\}", texto_resp)
                    if m_json:
                        resultado = json.loads(m_json.group(0))
                    else:
                        limpio = re.sub(r"^```(?:json)?\s*", "", texto_resp.strip(), flags=re.MULTILINE)
                        limpio = re.sub(r"```$", "", limpio.strip(), flags=re.MULTILINE)
                        resultado = json.loads(limpio)

                    mid = str(resultado.get("metodo_id", "")).lower().replace(" ", "").replace("_", "").replace("/", "")
                    if "13" in mid or "tercio" in mid:
                        resultado["metodo_id"] = "simpson13"
                    elif "38" in mid or "octavo" in mid:
                        resultado["metodo_id"] = "simpson38"
                    elif "trap" in mid:
                        resultado["metodo_id"] = "trapecio"
                    elif "gauss" in mid:
                        resultado["metodo_id"] = "gauss"
                    elif "newton" in mid or "cotes" in mid:
                        resultado["metodo_id"] = "newton"
                    elif "heun" in mid or "mejorado" in mid:
                        resultado["metodo_id"] = "euler_mejorado"
                    elif "euler" in mid:
                        resultado["metodo_id"] = "euler"
                    elif "rk" in mid or "runge" in mid:
                        resultado["metodo_id"] = "rk"
                    else:
                        resultado["metodo_id"] = "trapecio"

                    casillas_tuplas = []
                    for c in resultado.get("casillas", []):
                        if isinstance(c, dict):
                            campo = c.get("campo", c.get("nombre", c.get("casilla", "")))
                            val = str(c.get("valor", c.get("value", "")))
                            mot = c.get("motivo", c.get("explicacion", ""))
                            casillas_tuplas.append((campo, val, mot))
                        elif isinstance(c, (list, tuple)) and len(c) >= 2:
                            casillas_tuplas.append((str(c[0]), str(c[1]), str(c[2]) if len(c) > 2 else ""))
                    resultado["casillas"] = casillas_tuplas
                    return resultado
            except urllib.error.HTTPError as e:
                err_body = ""
                try:
                    err_body = e.read().decode("utf-8")
                except Exception:
                    pass
                ultimo_error = f"HTTP {e.code} ({e.reason}) en {modelo} ({api_ver}): {err_body[:200]}"
                break
            except Exception as e:
                ultimo_error = str(e)
                continue

    raise Exception(f"No se pudo completar la consulta con la API de Gemini ({ultimo_error})")


# ======================================================================
# 7. COMPONENTES VISUALES
# ======================================================================
class Caja:
    __slots__ = ("w", "asc", "desc", "dib")

    def __init__(self, w, asc, desc, dib):
        self.w, self.asc, self.desc, self.dib = w, asc, desc, dib


class Compositor:
    FUNCIONES = {"sen", "cos", "tg", "senh", "cosh", "tgh", "ln", "log", "exp",
                 "arcsen", "arccos", "arctg", "erf", "min", "max"}
    _TOK = re.compile(r"\\\\|\\[A-Za-z]+|\\.|\d+(?:\.\d+)?|[{}^_]|\s+|.", re.S)

    def __init__(self, familia, color):
        self.familia, self.color = familia, color
        self._fuentes = {}
        self._t, self._i = [], 0

    def fuente(self, px, cursiva=False, negrita=False):
        px = max(7, int(round(px)))
        clave = (px, cursiva, negrita)
        if clave not in self._fuentes:
            self._fuentes[clave] = tkfont.Font(family=self.familia, size=-px,
                                               slant="italic" if cursiva else "roman",
                                               weight="bold" if negrita else "normal")
        return self._fuentes[clave]

    def analizar(self, tex):
        self._t = self._TOK.findall(tex)
        self._i = 0
        return self._secuencia(set())

    def _ver(self):
        while self._i < len(self._t) and self._t[self._i].isspace():
            self._i += 1
        return self._t[self._i] if self._i < len(self._t) else None

    def _tomar(self):
        t = self._ver()
        if t is not None:
            self._i += 1
        return t

    def _secuencia(self, fin):
        items = []
        while True:
            t = self._ver()
            if t is None or t in fin:
                break
            items.append(self._atomo())
        return ("seq", items)

    def _atomo(self):
        base = self._base()
        sub = sup = None
        while self._ver() in ("^", "_"):
            op = self._tomar()
            arg = self._base()
            if op == "^":
                sup = arg
            else:
                sub = arg
        if sub is None and sup is None:
            return base
        return ("scripts", base, sub, sup)

    def _base(self):
        t = self._tomar()
        if t is None:
            return ("seq", [])
        if t == "{":
            sec = self._secuencia({"}"})
            self._tomar()
            return sec
        if t.startswith("\\") and len(t) > 1 and t != "\\\\":
            return self._comando(t[1:])
        if re.fullmatch(r"\d+(?:\.\d+)?", t):
            return ("num", t)
        if t.isalpha():
            return ("gri", t) if t in "ΣΔΩΠ" else ("var", t)
        if t in "+-−=<>≈≤≥·×±→":
            return ("op", "−" if t == "-" else t)
        if t == ",":
            return ("coma",)
        return ("sim", t)

    def _comando(self, n):
        if n == "frac":
            a = self._base()
            return ("frac", a, self._base())
        if n == "sqrt":
            return ("sqrt", self._base())
        if n == "bar":
            return ("bar", self._base())
        if n == "text":
            self._tomar()
            s = ""
            while self._i < len(self._t) and self._t[self._i] != "}":
                s += self._t[self._i]
                self._i += 1
            self._i += 1
            return ("txt", s)
        if n == "left":
            izq = self._tomar()
            cont = self._secuencia({"\\right"})
            self._tomar()
            return ("par", izq, cont, self._tomar())
        if n in ("sum", "int"):
            return ("bigop", n)
        if n == "substack":
            self._tomar()
            filas = []
            while True:
                filas.append(self._secuencia({"}", "\\\\"}))
                if self._ver() == "\\\\":
                    self._tomar()
                    continue
                break
            self._tomar()
            return ("stack", filas)
        espacios = {",": 0.17, ";": 0.3, " ": 0.3, "quad": 1.0, "qquad": 2.0, "!": -0.1}
        if n in espacios:
            return ("esp", espacios[n])
        simbolos = {"cdot": ("op", "·"), "approx": ("op", "≈"), "le": ("op", "≤"), "leq": ("op", "≤"),
                    "ge": ("op", "≥"), "geq": ("op", "≥"), "times": ("op", "×"), "pm": ("op", "±"),
                    "to": ("op", "→"), "pi": ("var", "π"), "Delta": ("gri", "Δ"), "infty": ("sim", "∞"),
                    "dots": ("sim", "…"), "ldots": ("sim", "…"), "square": ("sim", "□")}
        if n in simbolos:
            return simbolos[n]
        if n in self.FUNCIONES:
            return ("fn", n)
        return ("sim", n)

    def caja(self, nodo, px):
        return getattr(self, "_c_" + nodo[0])(nodo, px)

    def _texto(self, s, px, cursiva=False, pad_i=0, pad_d=0):
        f = self.fuente(px, cursiva)
        w = f.measure(s) + pad_i + pad_d + (int(px * 0.06) if cursiva else 0)
        bajo = int(px * 0.24) if any(ch in "gjpqy,;()[]|{}ȳ" for ch in s) else int(px * 0.02)
        desc_f, col = f.metrics("descent"), self.color

        def dib(cv, x, yb):
            cv.create_text(x + pad_i, yb + desc_f, text=s, font=f, fill=col, anchor="sw")
        return Caja(w, int(px * 0.74), bajo, dib)

    def _c_num(self, n, px):
        return self._texto(n[1], px)

    def _c_var(self, n, px):
        return self._texto(n[1], px, cursiva=True)

    def _c_gri(self, n, px):
        return self._texto(n[1], px)

    def _c_sim(self, n, px):
        return self._texto(n[1], px)

    def _c_txt(self, n, px):
        return self._texto(n[1], px)

    def _c_fn(self, n, px):
        return self._texto(n[1], px, pad_d=int(px * 0.12))

    def _c_coma(self, n, px):
        return self._texto(",", px, pad_d=int(px * 0.22))

    def _c_op(self, n, px):
        pad = int(px * 0.25)
        return self._texto(n[1], px, pad_i=pad, pad_d=pad)

    def _c_esp(self, n, px):
        return Caja(max(0, int(n[1] * px)), 0, 0, lambda cv, x, yb: None)

    def _c_seq(self, nodo, px):
        cajas, prev = [], None
        for h in nodo[1]:
            k = h[0]
            if k == "op":
                s = h[1]
                unario = s in ("+", "−") and (prev is None or prev in ("op", "coma", "abre"))
                if unario:
                    c = self._texto(s, px)
                else:
                    pad = int(px * (0.30 if s in "=≈≤≥→" else 0.20))
                    c = self._texto(s, px, pad_i=pad, pad_d=pad)
                prev = "op"
            else:
                c = self.caja(h, px)
                prev = "coma" if k == "coma" else ("abre" if (k == "sim" and h[1] in "([{|") else "otro")
            cajas.append(c)
        w = sum(c.w for c in cajas)
        asc = max([c.asc for c in cajas] + [0])
        desc = max([c.desc for c in cajas] + [0])

        def dib(cv, x, yb):
            for c in cajas:
                c.dib(cv, x, yb)
                x += c.w
        return Caja(w, asc, desc, dib)

    def _c_scripts(self, nodo, px):
        _, base, sub, sup = nodo
        if base[0] == "bigop":
            return self._bigop(base[1], sub, sup, px)
        B = self.caja(base, px)
        spx = px * 0.7
        S = self.caja(sup, spx) if sup else None
        D = self.caja(sub, spx) if sub else None
        su = max(0.42 * px, B.asc - 0.32 * px)
        sd = max(0.20 * px, B.desc + 0.05 * px)
        w = B.w + max(S.w if S else 0, D.w if D else 0) + 1
        asc = max(B.asc, (su + S.asc) if S else 0)
        desc = max(B.desc, (sd + D.desc) if D else 0)

        def dib(cv, x, yb):
            B.dib(cv, x, yb)
            if S:
                S.dib(cv, x + B.w + 1, yb - su)
            if D:
                D.dib(cv, x + B.w + 1, yb + sd)
        return Caja(w, asc, desc, dib)

    def _c_bigop(self, nodo, px):
        return self._bigop(nodo[1], None, None, px)

    def _bigop(self, tipo, lo, hi, px):
        L = self.caja(lo, px * 0.72) if lo else None
        H = self.caja(hi, px * 0.72) if hi else None
        eje = 0.30 * px
        if tipo == "sum":
            gp = px * 1.5
            f = self.fuente(gp)
            wg = f.measure("Σ")
            mitad = 0.36 * gp
            asc_g, desc_g = eje + mitad, max(0.0, mitad - eje)
            w = max(wg, L.w if L else 0, H.w if H else 0) + 2
            asc = asc_g + ((H.asc + H.desc + 3) if H else 0)
            desc = desc_g + ((L.asc + L.desc + 4) if L else 0)
            col, desc_f = self.color, f.metrics("descent")

            def dib(cv, x, yb):
                cv.create_text(x + (w - wg) / 2, yb - eje + mitad + desc_f, text="Σ", font=f, fill=col, anchor="sw")
                if H:
                    H.dib(cv, x + (w - H.w) / 2, yb - asc_g - 3 - H.desc)
                if L:
                    L.dib(cv, x + (w - L.w) / 2, yb + desc_g + 4 + L.asc)
            return Caja(w, asc, desc, dib)
        gp = px * 1.6
        f = self.fuente(gp)
        wg = f.measure("∫")
        asc_g, desc_g = eje + 0.52 * gp, max(0.0, 0.52 * gp - eje)
        xh, xl = wg * 1.0, wg * 0.4
        w = max(wg, xh + (H.w if H else 0), xl + (L.w if L else 0)) + 2
        col, desc_f = self.color, f.metrics("descent")

        def dib(cv, x, yb):
            cv.create_text(x, yb - eje + 0.30 * gp + desc_f, text="∫", font=f, fill=col, anchor="sw")
            if H:
                H.dib(cv, x + xh, yb - asc_g + H.asc)
            if L:
                L.dib(cv, x + xl, yb + desc_g - L.desc)
        return Caja(w, asc_g, desc_g, dib)

    def _c_frac(self, nodo, px):
        spx = px * 0.94
        N, D = self.caja(nodo[1], spx), self.caja(nodo[2], spx)
        eje, hueco = 0.30 * px, 0.14 * px
        w = max(N.w, D.w) + int(0.3 * px)
        asc = eje + hueco + N.desc + N.asc
        desc = max(0.0, D.asc + D.desc + hueco - eje)
        col = self.color

        def dib(cv, x, yb):
            cv.create_line(x + 0.05 * px, yb - eje, x + w - 0.05 * px, yb - eje, fill=col, width=1)
            N.dib(cv, x + (w - N.w) / 2, yb - eje - hueco - N.desc)
            D.dib(cv, x + (w - D.w) / 2, yb - eje + hueco + D.asc)
        return Caja(w + 2, asc, desc, dib)

    def _c_sqrt(self, nodo, px):
        C = self.caja(nodo[1], px)
        rw = 0.62 * px
        asc, desc = C.asc + 0.28 * px, C.desc + 1
        w = rw + C.w + 4
        col, lw = self.color, max(1, round(px / 13))

        def dib(cv, x, yb):
            arriba, abajo = yb - asc + 1, yb + desc
            medio = (arriba + abajo) / 2
            cv.create_line(x, medio + 0.1 * (abajo - arriba), x + 0.25 * rw, medio + 0.05 * (abajo - arriba),
                           x + 0.5 * rw, abajo, x + rw, arriba, x + w, arriba, fill=col, width=lw, joinstyle="miter")
            C.dib(cv, x + rw + 1, yb)
        return Caja(w, asc, desc, dib)

    def _c_bar(self, nodo, px):
        C = self.caja(nodo[1], px)
        asc = C.asc + 0.2 * px
        col = self.color

        def dib(cv, x, yb):
            C.dib(cv, x, yb)
            cv.create_line(x + 0.1 * C.w, yb - C.asc - 0.1 * px, x + 0.9 * C.w + 2, yb - C.asc - 0.1 * px, fill=col, width=1)
        return Caja(C.w, asc, C.desc, dib)

    def _c_par(self, nodo, px):
        izq, cont, der = nodo[1], nodo[2], nodo[3]
        C = self.caja(cont, px)
        asc, desc = max(C.asc, 0.78 * px) + 2, max(C.desc, 0.22 * px) + 2
        alto = asc + desc
        dw = max(0.30 * px, 0.10 * alto)
        wi = 0 if izq == "." else dw
        wd = 0 if der == "." else dw
        col, lw = self.color, max(1, round(px / 13))

        def delim(cv, d, x, yb, ancho, lado):
            if d == ".":
                return
            top, bot, mid = yb - asc, yb + desc, yb + (desc - asc) / 2
            a, b = (x + ancho * 0.85, x + ancho * 0.15) if lado == "i" else (x + ancho * 0.15, x + ancho * 0.85)
            if d in ("(", ")"):
                cv.create_line(a, top, b, mid, a, bot, smooth=True, splinesteps=12, fill=col, width=lw)
            elif d in ("[", "]"):
                cv.create_line(a, top, b, top, b, bot, a, bot, fill=col, width=lw)
            else:
                cv.create_line(x + ancho / 2, top, x + ancho / 2, bot, fill=col, width=lw)

        def dib(cv, x, yb):
            delim(cv, izq, x + 1, yb, wi, "i")
            C.dib(cv, x + 1 + wi + 2, yb)
            delim(cv, der, x + 1 + wi + 2 + C.w + 2, yb, wd, "d")
        return Caja(wi + C.w + wd + 6, asc, desc, dib)

    def _c_stack(self, nodo, px):
        filas = [self.caja(f, px) for f in nodo[1]]
        w = max(c.w for c in filas)
        pos, y = [], 0.0
        for i, c in enumerate(filas):
            y += c.asc if i == 0 else (filas[i - 1].desc + 1 + c.asc)
            pos.append(y)
        asc, desc = filas[0].asc, pos[-1] - filas[0].asc + filas[-1].desc

        def dib(cv, x, yb):
            for c, p in zip(filas, pos):
                c.dib(cv, x + (w - c.w) / 2, yb + p - filas[0].asc)
        return Caja(w, asc, desc, dib)


class LienzoFormula(tk.Canvas):
    def __init__(self, master, comp, px, fondo, fam_ui, color, mudo, px_texto, centrar=False, alto_fijo=None, margen=12):
        super().__init__(master, bg=fondo, highlightthickness=0, height=alto_fijo or 40)
        self.comp, self.px, self.fondo = comp, px, fondo
        self.fam_ui, self.color, self.mudo, self.px_texto = fam_ui, color, mudo, px_texto
        self.centrar, self.alto_fijo, self.margen = centrar, alto_fijo, margen
        self.items = []
        self._fuentes_ui = {}
        self.bind("<Configure>", lambda e: self.redibujar())

    def mostrar(self, items):
        self.items = items
        self.redibujar()

    def _fuente_ui(self, px, negrita=False):
        clave = (max(8, int(px)), negrita)
        if clave not in self._fuentes_ui:
            self._fuentes_ui[clave] = tkfont.Font(family=self.fam_ui, size=-clave[0], weight="bold" if negrita else "normal")
        return self._fuentes_ui[clave]

    def _caja(self, item, px, disp):
        tipo = item[0]
        if tipo == "m":
            return self.comp.caja(self.comp.analizar(item[1]), px)
        if tipo == "t":
            f = self._fuente_ui(min(self.px_texto, px * 0.9))
            s, col = item[1], (item[2] if len(item) > 2 else self.mudo)
            desc_f = f.metrics("descent")
            return Caja(f.measure(s), int(f.metrics("ascent") * 0.85), desc_f,
                        lambda cv, x, yb: cv.create_text(x, yb + desc_f, text=s, font=f, fill=col, anchor="sw"))
        return self._tabla(item[1], px, disp)

    def _tabla(self, filas, px, disp):
        f = self._fuente_ui(min(self.px_texto * 1.05, px * 0.85))
        fb = self._fuente_ui(min(self.px_texto * 1.05, px * 0.85), True)
        alto_f = f.metrics("linespace") + 8
        pad = 18

        def anchos(cols):
            return [max(f.measure(str(fila[c])) for fila in filas if c < len(fila)) + pad for c in cols]
        n = max(len(fila) for fila in filas)
        cols = list(range(n))
        w = sum(anchos(cols))
        if w > disp and n > 3:
            k = n
            while k > 2 and sum(anchos(list(range(k - 1)))) + f.measure("…") + pad > disp:
                k -= 1
            filas = [list(fila[:k - 1]) + ["…"] for fila in filas]
            cols = list(range(k))
        ws = anchos(cols)
        total, col, linea, desc_f = sum(ws), self.color, self.mudo, f.metrics("descent")

        def dib(cv, x, yb):
            y0 = yb - alto_f * len(filas)
            cv.create_rectangle(x, y0, x + total, yb, outline=linea)
            for i, fila in enumerate(filas):
                if i:
                    cv.create_line(x, y0 + i * alto_f, x + total, y0 + i * alto_f, fill=linea)
                cx = x
                for c, wc in zip(cols, ws):
                    if c:
                        cv.create_line(cx, y0 + i * alto_f, cx, y0 + (i + 1) * alto_f, fill=linea)
                    txt = str(fila[c]) if c < len(fila) else ""
                    cv.create_text(cx + wc / 2, y0 + (i + 1) * alto_f - 4 + desc_f, text=txt, anchor="s",
                                   font=fb if c == 0 else f, fill=col)
                    cx += wc
        return Caja(total, alto_f * len(filas), 0, dib)

    def redibujar(self):
        self.delete("all")
        w = self.winfo_width()
        if w < 40 or not self.items:
            return
        disp = w - 2 * self.margen
        mv = 10
        escala = 1.0
        for _ in range(6):
            cajas = [self._caja(it, self.px * escala, disp) for it in self.items]
            gap = 0.5 * self.px * escala
            ancho = max(c.w for c in cajas)
            alto = sum(c.asc + c.desc for c in cajas) + gap * (len(cajas) - 1)
            ajuste = 1.0
            if ancho > disp:
                ajuste = min(ajuste, disp / ancho * 0.985)
            if self.alto_fijo and alto > self.alto_fijo - 2 * mv:
                ajuste = min(ajuste, (self.alto_fijo - 2 * mv) / alto * 0.985)
            if ajuste >= 0.999 or self.px * escala <= 9:
                break
            escala *= ajuste
        total_alto = int(alto + 2 * mv)
        if not self.alto_fijo and int(self.cget("height")) != total_alto:
            self.configure(height=total_alto)
        alto_disp = self.alto_fijo or total_alto
        y = max(mv, (alto_disp - alto) / 2) if (self.alto_fijo or self.centrar) else mv
        for c in cajas:
            x = (w - c.w) / 2 if self.centrar else self.margen
            c.dib(self, x, y + c.asc)
            y += c.asc + c.desc + gap


def construir_vista(metodo, v, modo):
    tipo, malos = metodo["vista"], []

    def T(clave, variables, nombre, envolver=False):
        t, _ = _tex_de(v.get(clave, ""), variables, envolver)
        if t is None:
            malos.append(nombre)
            return "\\text{?}"
        return t

    if tipo == "edo":
        f = T("f", ("x", "y"), "f(x, y)")
        x0, y0, xf = T("x0", (), "x0"), T("y0", (), "y0"), T("xf", (), "xf")
        items = [("m", "\\frac{dy}{dx} = " + f), ("m", f"y({x0}) = {y0},\\quad y({xf}) = \\,?")]
        try:
            n = leer_entero(v["n"], "n")
            pie = f"n = {n} subintervalos" + (f",  Runge-Kutta de orden {v['orden']}" if "orden" in v else "")
            items.append(("t", pie))
        except ErrorMatematico:
            malos.append("n")
    elif modo == "tabla":
        xs = [t for t in re.split(r"[,;\s]+", (v.get("xs") or "").strip()) if t]
        ys = [t for t in re.split(r"[,;\s]+", (v.get("ys") or "").strip()) if t]
        filas = [["x"] + xs, ["f(x)"] + ys]
        desde = (v.get("ta") or "").strip() or (xs[0] if xs else "?")
        hasta = (v.get("tb") or "").strip() or (xs[-1] if xs else "?")
        items = [("tabla", filas), ("t", f"Área bajo la curva entre x = {desde} y x = {hasta}")]
        if len(xs) != len(ys):
            items.append(("t", f"Hay {len(xs)} valores de x y {len(ys)} de f(x): deben ser iguales.", C["error"]))
    else:
        a, b = T("a", (), "a"), T("b", (), "b")
        f = T("f", ("x",), "f(x)", envolver=True)
        items = [("m", f"\\int_{{{a}}}^{{{b}}} {f}\\,dx")]
        try:
            if tipo == "gauss":
                items.append(("t", f"{leer_entero(v['npuntos'], 'n')} puntos de Gauss"))
            else:
                n = leer_entero(v["n"], "n")
                pie = f"n = {n} subintervalos"
                try:
                    pie += f",   h = {g((leer_numero(v['b'], 'b') - leer_numero(v['a'], 'a')) / n)}"
                except ErrorMatematico:
                    pass
                items.append(("t", pie))
        except ErrorMatematico:
            malos.append("n")
    if malos:
        items.append(("t", "Revisa: " + ", ".join(dict.fromkeys(malos)) + " (aún no es una expresión válida)", C["aviso"]))
    return items


def _tex_de(texto, variables, envolver=False):
    if not (texto or "").strip():
        return "\\square", None
    try:
        return a_tex(texto, variables, envolver), None
    except ErrorMatematico as e:
        return None, str(e)


class Boton(tk.Label):
    def __init__(self, master, texto, comando, color, hover, fg="white", fuente=None, padx=18, pady=9):
        super().__init__(master, text=texto, bg=color, fg=fg, font=fuente, padx=padx, pady=pady, cursor="hand2")
        self._color, self._hover, self._comando = color, hover, comando
        self.bind("<Enter>", lambda e: self.configure(bg=self._hover))
        self.bind("<Leave>", lambda e: self.configure(bg=self._color))
        self.bind("<Button-1>", lambda e: self._comando())

    def colorear(self, color, hover, fg):
        self._color, self._hover = color, hover
        self.configure(bg=color, fg=fg)


class ItemMenu(tk.Frame):
    def __init__(self, master, metodo, comando, fuentes, insignia_color=None):
        super().__init__(master, bg=C["tinta"], cursor="hand2")
        self.activo = False
        self.insignia_color = insignia_color or C["tinta_2"]
        self.insignia = tk.Label(self, text=metodo["insignia"], bg=self.insignia_color, fg="white", width=4,
                                 font=fuentes["insignia"], pady=6)
        self.insignia.grid(row=0, column=0, rowspan=2, padx=(14, 10), pady=5)
        self.titulo = tk.Label(self, text=metodo["nombre"], bg=C["tinta"], fg="white", font=fuentes["negrita"], anchor="w")
        self.titulo.grid(row=0, column=1, sticky="w", pady=(5, 0))
        self.sub = tk.Label(self, text=metodo["sub"], bg=C["tinta"], fg=C["tinta_texto"], font=fuentes["pequena"], anchor="w")
        self.sub.grid(row=1, column=1, sticky="w", pady=(0, 5))
        self.columnconfigure(1, weight=1)
        for w in (self, self.insignia, self.titulo, self.sub):
            w.bind("<Button-1>", lambda e: comando())
            w.bind("<Enter>", lambda e: self._pintar(True))
            w.bind("<Leave>", lambda e: self._pintar(False))
        self._pintar(False)

    def _pintar(self, encima):
        fondo = C["acento"] if self.activo else (C["tinta_2"] if encima else C["tinta"])
        insignia = C["acento_osc"] if self.activo else self.insignia_color
        for w in (self, self.titulo, self.sub):
            w.configure(bg=fondo)
        self.insignia.configure(bg=insignia if not (encima and not self.activo) else C["tinta"])
        self.sub.configure(fg="white" if self.activo else C["tinta_texto"])

    def activar(self, si):
        self.activo = si
        self._pintar(False)


class Grafica(tk.Canvas):
    def __init__(self, master, fuente, fuente_peq):
        super().__init__(master, bg="white", highlightthickness=0)
        self.fuente, self.fuente_peq = fuente, fuente_peq
        self.spec = None
        self.bind("<Configure>", lambda e: self.redibujar())

    def mostrar(self, spec):
        self.spec = spec
        self.redibujar()

    def redibujar(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 80 or h < 80:
            return
        if not self.spec or not self.spec["capas"]:
            self.create_text(w / 2, h / 2, text="La gráfica aparece aquí después de calcular",
                             fill=C["apagado"], font=self.fuente)
            return
        capas = self.spec["capas"]
        puntos = [p for c in capas for p in c["pts"]]
        if not puntos:
            return
        xmin, xmax = min(p[0] for p in puntos), max(p[0] for p in puntos)
        ymin, ymax = min(min(p[1] for p in puntos), 0), max(max(p[1] for p in puntos), 0)
        if xmax == xmin:
            xmin, xmax = xmin - 1, xmax + 1
        if ymax == ymin:
            ymin, ymax = ymin - 1, ymax + 1
        margen_y = (ymax - ymin) * 0.08
        ymax += margen_y
        ymin = ymin - margen_y if ymin < 0 else 0
        izq, der, arr, aba = 62, 22, 58, 36
        ancho, alto = w - izq - der, h - arr - aba

        def px(x):
            return izq + (x - xmin) / (xmax - xmin) * ancho

        def py(y):
            return arr + (ymax - y) / (ymax - ymin) * alto

        for i in range(6):
            x = xmin + (xmax - xmin) * i / 5
            self.create_line(px(x), arr, px(x), arr + alto, fill="#E3EAF0")
            self.create_text(px(x), arr + alto + 14, text=f"{x:.4g}", fill=C["apagado"], font=self.fuente_peq)
            y = ymin + (ymax - ymin) * i / 5
            self.create_line(izq, py(y), izq + ancho, py(y), fill="#E3EAF0")
            self.create_text(izq - 8, py(y), text=f"{y:.4g}", fill=C["apagado"], font=self.fuente_peq, anchor="e")
        if ymin <= 0 <= ymax:
            self.create_line(izq, py(0), izq + ancho, py(0), fill=C["apagado"], width=1)
        self.create_text(izq, 16, text=self.spec["titulo"], fill=C["texto"], font=self.fuente, anchor="w")

        for capa in capas:
            coords = []
            for x, y in capa["pts"]:
                coords += [px(x), py(y)]
            tipo = capa["tipo"]
            if tipo == "area" and len(coords) >= 6:
                self.create_polygon(coords, fill=capa["relleno"], outline=capa["borde"], width=1)
            elif tipo == "linea" and len(coords) >= 4:
                self.create_line(coords, fill=capa["color"], width=capa.get("ancho", 2),
                                 dash=(5, 4) if capa.get("punteado") else None)
            elif tipo == "puntos":
                for x, y in capa["pts"]:
                    self.create_oval(px(x) - 3.5, py(y) - 3.5, px(x) + 3.5, py(y) + 3.5,
                                     fill=capa["color"], outline="white")
        x_ley = izq
        for capa in [c for c in capas if c.get("leyenda")]:
            self.create_line(x_ley, 38, x_ley + 20, 38, fill=capa["color"], width=3,
                             dash=(4, 3) if capa.get("punteado") else None)
            self.create_text(x_ley + 26, 38, text=capa["leyenda"], fill=C["texto"], font=self.fuente_peq, anchor="w")
            x_ley += 26 + len(capa["leyenda"]) * 7 + 22


# ======================================================================
# 8. VENTANA PRINCIPAL
# ======================================================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Calculadora de métodos numéricos")
        self.k = max(1.0, float(self.tk.call("tk", "scaling")) / 1.3333)
        ancho = min(int(1320 * self.k), self.winfo_screenwidth() - 60)
        alto = min(int(820 * self.k), self.winfo_screenheight() - 100)
        self.geometry(f"{ancho}x{alto}+30+20")
        self.minsize(min(1100, ancho), min(680, alto))
        self.configure(bg=C["papel"])

        self._vista_job = None
        self._crear_fuentes()
        self._crear_estilos()
        self.comp = Compositor(self.fam_serif, C["texto"])

        self.vars = {}
        self.modos = {}
        for m in METODOS:
            self.vars[m["id"]] = {}
            for c in m["campos"]:
                var = tk.BooleanVar(value=c["defecto"]) if c["tipo"] == "check" else tk.StringVar(value=c["defecto"])
                var.trace_add("write", self._programar_vista)
                self.vars[m["id"]][c["clave"]] = var
            self.modos[m["id"]] = tk.StringVar(value="funcion")
            self.modos[m["id"]].trace_add("write", self._programar_vista)

        self.decimales = tk.StringVar(value="6")
        self.ayuda = tk.StringVar(value="")
        self.metodo = METODOS[0]
        self.items = {}
        self.modo_asistente_activo = False
        self.resultado_ia_actual = None

        self.var_modo_ia = tk.StringVar(value="gemini")
        self.var_api_key = tk.StringVar(value=API_KEY_PREDETERMINADA)

        self.columnconfigure(2, weight=1)
        self.rowconfigure(0, weight=1)

        self._crear_barra_lateral()
        self._crear_panel_datos()
        self._crear_panel_resultados()
        self._crear_panel_asistente_ia()

        self.bind("<Return>", self._on_enter)
        self.bind("<KP_Enter>", self._on_enter)
        self.seleccionar_metodo(METODOS[0])

    def _on_enter(self, event=None):
        if not self.modo_asistente_activo:
            self.calcular()

    def _crear_fuentes(self):
        disponibles = set(tkfont.families())

        def elegir(candidatas, defecto):
            for c in candidatas:
                if c in disponibles:
                    return c
            return defecto

        ui = elegir(["Segoe UI", "SF Pro Text", "Helvetica Neue", "Ubuntu", "Noto Sans", "DejaVu Sans"], "TkDefaultFont")
        mono = elegir(["Cascadia Mono", "Consolas", "Menlo", "JetBrains Mono", "DejaVu Sans Mono", "Courier New"], "TkFixedFont")
        self.fam_serif = elegir(["Cambria", "Cambria Math", "STIX Two Text", "STIXGeneral", "Times New Roman",
                                 "Georgia", "DejaVu Serif"], "TkDefaultFont")
        self.fam_ui = ui
        self.f = {
            "base": (ui, 10),
            "negrita": (ui, 10, "bold"),
            "pequena": (ui, 9),
            "insignia": (ui, 9, "bold"),
            "titulo": (ui, 17, "bold"),
            "titulo_lateral": (ui, 15, "bold"),
            "seccion": (ui, 12, "bold"),
            "grande": (ui, 30, "bold"),
            "mono": (mono, 10),
        }
        self.option_add("*TCombobox*Listbox.font", self.f["base"])

    def _crear_estilos(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure("Campo.TEntry", fieldbackground="white", foreground=C["texto"], bordercolor=C["linea"],
                    lightcolor=C["linea"], darkcolor=C["linea"], padding=6)
        s.map("Campo.TEntry", bordercolor=[("focus", C["acento"])], lightcolor=[("focus", C["acento"])],
              darkcolor=[("focus", C["acento"])])
        s.configure("Campo.TCombobox", fieldbackground="white", background="white", foreground=C["texto"],
                    bordercolor=C["linea"], lightcolor=C["linea"], darkcolor=C["linea"], arrowcolor=C["acento"], padding=5)
        s.map("Campo.TCombobox", fieldbackground=[("readonly", "white")], bordercolor=[("focus", C["acento"])])
        s.configure("TNotebook", background=C["papel"], borderwidth=0)
        s.configure("TNotebook.Tab", padding=(20, 9), font=self.f["negrita"], background=C["papel"],
                    foreground=C["apagado"], borderwidth=0)
        s.map("TNotebook.Tab", background=[("selected", C["tarjeta"])], foreground=[("selected", C["acento_osc"])])
        s.configure("Treeview", rowheight=int(27 * self.k), background="white", fieldbackground="white",
                    foreground=C["texto"], borderwidth=0, font=self.f["base"])
        s.configure("Treeview.Heading", background=C["acento_suave"], foreground=C["acento_osc"],
                    font=self.f["negrita"], relief="flat", padding=7)
        s.map("Treeview", background=[("selected", C["acento"])], foreground=[("selected", "white")])
        s.configure("TSpinbox", fieldbackground="white", bordercolor=C["linea"], arrowcolor=C["acento"], padding=4)

    def _tarjeta(self, master):
        return tk.Frame(master, bg=C["tarjeta"], highlightbackground=C["linea"], highlightthickness=1)

    def _crear_barra_lateral(self):
        lat = tk.Frame(self, bg=C["tinta"], width=int(268 * self.k))
        lat.grid(row=0, column=0, sticky="ns")
        lat.pack_propagate(False)

        tk.Label(lat, text="Métodos numéricos", bg=C["tinta"], fg="white", font=self.f["titulo_lateral"],
                 anchor="w").pack(fill="x", padx=18, pady=(22, 0))
        tk.Label(lat, text="Calculadora con paso a paso", bg=C["tinta"], fg=C["tinta_texto"],
                 font=self.f["base"], anchor="w").pack(fill="x", padx=18, pady=(2, 14))

        tk.Label(lat, text="ASISTENTE INTELIGENTE", bg=C["tinta"], fg="#FBBF24", font=self.f["negrita"],
                 anchor="w").pack(fill="x", padx=18, pady=(4, 4))

        meta_ia = dict(id="asistente_ia", nombre="Buscador con IA", sub="Identifica método y datos", insignia="✨ IA")
        self.item_asistente_ia = ItemMenu(lat, meta_ia, self.mostrar_asistente_ia, self.f, insignia_color=C["ia_morado"])
        self.item_asistente_ia.pack(fill="x", pady=(0, 10))

        grupo_actual = None
        for m in METODOS:
            if m["grupo"] != grupo_actual:
                grupo_actual = m["grupo"]
                tk.Label(lat, text=grupo_actual, bg=C["tinta"], fg=C["tinta_texto"], font=self.f["negrita"],
                         anchor="w").pack(fill="x", padx=18, pady=(14, 4))
            item = ItemMenu(lat, m, lambda mm=m: self.seleccionar_metodo(mm), self.f)
            item.pack(fill="x")
            self.items[m["id"]] = item

        tk.Label(lat, text="Realizado Por: Alejandro Castro Palacio \nIngeniero Multimedia", bg=C["tinta"],
                 fg=C["tinta_texto"], font=self.f["pequena"], justify="left", anchor="w").pack(
            side="bottom", fill="x", padx=18, pady=16)

    def _crear_panel_datos(self):
        col = tk.Frame(self, bg=C["papel"], width=int(530 * self.k))
        self.panel_datos = col
        col.grid(row=0, column=1, sticky="ns", padx=(18, 9), pady=18)
        col.grid_propagate(False)
        col.columnconfigure(0, weight=1)
        col.rowconfigure(1, weight=1)
        px_cap = int(12 * self.k)

        tv = self._tarjeta(col)
        tv.grid(row=0, column=0, sticky="ew", pady=(0, 12))
        tk.Label(tv, text="Así se ve tu problema", bg=C["tarjeta"], fg=C["apagado"], font=self.f["pequena"],
                 anchor="w").pack(fill="x", padx=14, pady=(8, 0))
        self.vista = LienzoFormula(tv, self.comp, px=int(22 * self.k), fondo=C["tarjeta"], fam_ui=self.fam_ui,
                                   color=C["texto"], mudo=C["apagado"], px_texto=px_cap, centrar=True,
                                   alto_fijo=int(118 * self.k))
        self.vista.pack(fill="x", padx=8, pady=(0, 6))

        self.zona = tk.Frame(col, bg=C["papel"])
        self.zona.grid(row=1, column=0, sticky="nsew")
        self.zona.columnconfigure(0, weight=1)
        self.zona.rowconfigure(0, weight=1)
        self.lienzo = tk.Canvas(self.zona, bg=C["papel"], highlightthickness=0, yscrollincrement=24)
        self.barra_datos = ttk.Scrollbar(self.zona, orient="vertical", command=self.lienzo.yview)
        self.lienzo.configure(yscrollcommand=self.barra_datos.set)
        self.lienzo.grid(row=0, column=0, sticky="nsew")
        self.barra_datos.grid(row=0, column=1, sticky="ns", padx=(6, 0))
        interior = tk.Frame(self.lienzo, bg=C["papel"])
        interior.columnconfigure(0, weight=1)
        ventana = self.lienzo.create_window((0, 0), window=interior, anchor="nw")
        interior.bind("<Configure>", self._ajustar_scroll)
        self.lienzo.bind("<Configure>", lambda e: (self.lienzo.itemconfigure(ventana, width=e.width), self._ajustar_scroll()))
        for evento in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.bind_all(evento, self._rueda, add="+")

        tf = self._tarjeta(interior)
        tf.grid(row=0, column=0, sticky="ew")
        self.lbl_nombre = tk.Label(tf, bg=C["tarjeta"], fg=C["texto"], font=self.f["seccion"], anchor="w")
        self.lbl_nombre.pack(fill="x", padx=16, pady=(14, 8))
        self.formula_cv = LienzoFormula(tf, self.comp, px=int(16 * self.k), fondo=C["acento_suave"], fam_ui=self.fam_ui,
                                        color=C["texto"], mudo=C["apagado"], px_texto=px_cap, margen=14)
        self.formula_cv.pack(fill="x", padx=16)
        self.lbl_desc = tk.Label(tf, bg=C["tarjeta"], fg=C["apagado"], font=self.f["base"], justify="left",
                                 anchor="w", wraplength=int(440 * self.k))
        self.lbl_desc.pack(fill="x", padx=16, pady=(10, 14))

        td = self._tarjeta(interior)
        td.grid(row=1, column=0, sticky="ew", pady=(14, 4))
        td.columnconfigure(0, weight=1)
        tk.Label(td, text="Datos", bg=C["tarjeta"], fg=C["texto"], font=self.f["seccion"], anchor="w").grid(
            row=0, column=0, sticky="w", padx=16, pady=(14, 6))
        self.marco_modo = tk.Frame(td, bg=C["tarjeta"])
        self.marco_modo.grid(row=1, column=0, sticky="w", padx=16)
        self.btn_funcion = Boton(self.marco_modo, "Función f(x)", lambda: self._cambiar_modo("funcion"),
                                 C["acento"], C["acento_osc"], fuente=self.f["negrita"], padx=14, pady=6)
        self.btn_funcion.pack(side="left")
        self.btn_tabla = Boton(self.marco_modo, "Tabla de datos", lambda: self._cambiar_modo("tabla"),
                               C["acento_suave"], C["linea"], fg=C["acento_osc"], fuente=self.f["negrita"], padx=14, pady=6)
        self.btn_tabla.pack(side="left", padx=(6, 0))
        self.marco_campos = tk.Frame(td, bg=C["tarjeta"])
        self.marco_campos.grid(row=2, column=0, sticky="ew", padx=16, pady=(10, 4))
        self.marco_campos.columnconfigure(1, weight=1)
        self.lbl_ayuda = tk.Label(td, textvariable=self.ayuda, bg=C["tarjeta"], fg=C["apagado"], font=self.f["pequena"],
                                  justify="left", anchor="nw", wraplength=int(440 * self.k), height=3)
        self.lbl_ayuda.grid(row=3, column=0, sticky="ew", padx=16, pady=(2, 12))

        acciones = tk.Frame(col, bg=C["papel"])
        acciones.grid(row=2, column=0, sticky="ew", pady=(12, 0))
        acciones.columnconfigure(0, weight=1)
        fila1 = tk.Frame(acciones, bg=C["papel"])
        fila1.grid(row=0, column=0, sticky="ew")
        Boton(fila1, "Calcular   (Enter)", self.calcular, C["acento"], C["acento_osc"], fuente=self.f["negrita"],
              padx=26, pady=11).pack(side="left")
        Boton(fila1, "Restablecer", self.restablecer, C["tarjeta"], C["linea"], fg=C["texto"], fuente=self.f["negrita"],
              padx=18, pady=11).pack(side="left", padx=(10, 0))
        fila2 = tk.Frame(acciones, bg=C["papel"])
        fila2.grid(row=1, column=0, sticky="ew", pady=(12, 0))
        fila2.columnconfigure(0, weight=1)
        self.combo_ej = ttk.Combobox(fila2, state="readonly", style="Campo.TCombobox", font=self.f["base"])
        self.combo_ej.grid(row=0, column=0, sticky="ew")
        self.combo_ej.bind("<<ComboboxSelected>>", self._aplicar_ejemplo)
        tk.Label(fila2, text="Decimales", bg=C["papel"], fg=C["apagado"], font=self.f["base"]).grid(
            row=0, column=1, padx=(14, 6))
        ttk.Spinbox(fila2, from_=1, to=12, width=4, textvariable=self.decimales, style="TSpinbox",
                    font=self.f["base"]).grid(row=0, column=2)

    def _ajustar_scroll(self, event=None):
        caja = self.lienzo.bbox("all")
        self.lienzo.configure(scrollregion=caja)
        if caja and caja[3] > self.lienzo.winfo_height():
            self.barra_datos.grid()
        else:
            self.barra_datos.grid_remove()
            self.lienzo.yview_moveto(0)

    def _rueda(self, e):
        w = self.winfo_containing(e.x_root, e.y_root)
        if w is None or not str(w).startswith(str(self.zona)):
            return
        caja = self.lienzo.bbox("all")
        if not caja or caja[3] <= self.lienzo.winfo_height():
            return
        paso = -1 if (e.num == 4 or getattr(e, "delta", 0) > 0) else 1
        self.lienzo.yview_scroll(paso * 2, "units")

    def _refrescar_formula(self, event=None):
        m = self.metodo
        lineas = m["formula"]
        if m.get("formula_por"):
            clave, tabla = m["formula_por"]
            lineas = tabla.get(self.vars[m["id"]][clave].get(), lineas)
        self.formula_cv.mostrar([("t", ln[1:]) if ln.startswith("#") else ("m", ln) for ln in lineas])
        self._programar_vista()

    def _programar_vista(self, *args):
        if self._vista_job is not None:
            self.after_cancel(self._vista_job)
        self._vista_job = self.after(120, self._actualizar_vista)

    def _actualizar_vista(self):
        self._vista_job = None
        if self.modo_asistente_activo:
            return
        m = self.metodo
        v = {k: var.get() for k, var in self.vars[m["id"]].items()}
        modo = self.modos[m["id"]].get() if m["tabla"] else "funcion"
        try:
            items = construir_vista(m, v, modo)
        except Exception:
            items = [("t", "Termina de escribir para ver la vista previa.")]
        self.vista.mostrar(items)

    def _crear_panel_resultados(self):
        col = tk.Frame(self, bg=C["papel"])
        self.panel_resultados = col
        col.grid(row=0, column=2, sticky="nsew", padx=(9, 18), pady=18)
        col.columnconfigure(0, weight=1)
        col.rowconfigure(1, weight=1)

        self.banner = tk.Frame(col, bg=C["tarjeta"], highlightbackground=C["linea"], highlightthickness=1)
        self.banner.grid(row=0, column=0, sticky="ew")
        self.b_etq = tk.Label(self.banner, text="", bg=C["tarjeta"], fg=C["apagado"], font=self.f["negrita"], anchor="w")
        self.b_etq.pack(fill="x", padx=18, pady=(14, 0))
        self.b_val = tk.Label(self.banner, text="", bg=C["tarjeta"], fg=C["texto"], font=self.f["grande"], anchor="w")
        self.b_val.pack(fill="x", padx=18)
        self.b_sub = tk.Label(self.banner, text="", bg=C["tarjeta"], fg=C["apagado"], font=self.f["base"],
                              anchor="w", justify="left")
        self.b_sub.pack(fill="x", padx=18, pady=(0, 14))
        self.banner.bind("<Configure>", lambda e: self.b_sub.configure(wraplength=max(200, e.width - 40)))
        self._pintar_banner("neutro", "Listo para calcular", "—",
                            "Elige un método, revisa los datos y presiona Calcular o la tecla Enter.")

        self.nb = ttk.Notebook(col)
        self.nb.grid(row=1, column=0, sticky="nsew", pady=(14, 0))

        tab1 = tk.Frame(self.nb, bg=C["tarjeta"])
        self.nb.add(tab1, text="Paso a paso")
        self.txt = tk.Text(tab1, wrap="word", bg=C["tarjeta"], fg=C["texto"], font=self.f["base"], relief="flat",
                           padx=18, pady=10, highlightthickness=0, cursor="arrow", state="disabled")
        sb = ttk.Scrollbar(tab1, command=self.txt.yview)
        self.txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.txt.pack(side="left", fill="both", expand=True)
        self.txt.tag_configure("titulo", font=self.f["negrita"], foreground=C["acento_osc"], spacing1=14, spacing3=4)
        self.txt.tag_configure("texto", font=self.f["base"], foreground=C["texto"], spacing3=4)
        self.txt.tag_configure("formula", font=self.f["mono"], background="#F2F6F9", lmargin1=12, lmargin2=12,
                               spacing1=2, spacing3=2)
        self.txt.tag_configure("resultado", font=self.f["seccion"], foreground=C["ok"], background=C["ok_suave"],
                               lmargin1=12, lmargin2=12, spacing1=4, spacing3=4)
        self.txt.tag_configure("aviso", foreground=C["aviso"], background=C["aviso_suave"], lmargin1=12, lmargin2=12,
                               spacing1=6, spacing3=4)
        self.txt.tag_configure("error", foreground=C["error"], background=C["error_suave"], lmargin1=12, lmargin2=12,
                               spacing1=4, spacing3=4)

        ui = self.fam_ui
        self.txt.tag_configure("sup1", font=(ui, 8), offset=int(5 * self.k))
        self.txt.tag_configure("sup2", font=(ui, 7), offset=int(8 * self.k))
        self.txt.tag_configure("sub1", font=(ui, 8), offset=-int(3 * self.k))

        tab2 = tk.Frame(self.nb, bg=C["tarjeta"])
        self.nb.add(tab2, text="Tabla de valores")
        self.tree = ttk.Treeview(tab2, show="headings")
        sbv = ttk.Scrollbar(tab2, command=self.tree.yview)
        sbh = ttk.Scrollbar(tab2, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=sbv.set, xscrollcommand=sbh.set)
        sbv.pack(side="right", fill="y")
        sbh.pack(side="bottom", fill="x")
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.tag_configure("par", background="#F4F8FB")

        tab3 = tk.Frame(self.nb, bg=C["tarjeta"])
        self.nb.add(tab3, text="Gráfica")
        self.grafica = Grafica(tab3, self.f["negrita"], self.f["pequena"])
        self.grafica.pack(fill="both", expand=True)

    def _crear_panel_asistente_ia(self):
        self.panel_ia = tk.Frame(self, bg=C["papel"])
        self.panel_ia.columnconfigure(0, weight=4)
        self.panel_ia.columnconfigure(1, weight=5)
        self.panel_ia.rowconfigure(0, weight=1)

        col_izq = self._tarjeta(self.panel_ia)
        col_izq.grid(row=0, column=0, sticky="nsew", padx=(18, 9), pady=18)
        col_izq.columnconfigure(0, weight=1)
        col_izq.rowconfigure(2, weight=1)

        cab = tk.Frame(col_izq, bg=C["tarjeta"])
        cab.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 6))
        tk.Label(cab, text="✨ Asistente IA / Buscador de Métodos", bg=C["tarjeta"], fg=C["ia_morado"],
                 font=self.f["titulo_lateral"]).pack(anchor="w")
        tk.Label(cab, text="Describe o pega el enunciado de tu ejercicio. La IA identificará el método exacto,\n"
                           "te dirá de qué orden es, por qué se debe usar y qué valores poner en cada casilla.",
                 bg=C["tarjeta"], fg=C["apagado"], font=self.f["base"], justify="left").pack(anchor="w", pady=(4, 0))

        cfg_modo = tk.Frame(col_izq, bg=C["acento_suave"], padx=12, pady=10)
        cfg_modo.grid(row=1, column=0, sticky="ew", padx=18, pady=(6, 12))
        cfg_modo.columnconfigure(1, weight=1)

        tk.Label(cfg_modo, text="Motor de análisis:", bg=C["acento_suave"], fg=C["acento_osc"],
                 font=self.f["negrita"]).grid(row=0, column=0, sticky="w")

        r1 = tk.Radiobutton(cfg_modo, text="API Gemini Online (Recomendado)",
                            variable=self.var_modo_ia, value="gemini", bg=C["acento_suave"],
                            fg=C["texto"], font=self.f["pequena"], command=self._actualizar_modo_ia)
        r1.grid(row=0, column=1, sticky="w", padx=10)

        r2 = tk.Radiobutton(cfg_modo, text="Analizador Local Experto (Offline)",
                            variable=self.var_modo_ia, value="heuristico", bg=C["acento_suave"],
                            fg=C["texto"], font=self.f["pequena"], command=self._actualizar_modo_ia)
        r2.grid(row=1, column=1, sticky="w", padx=10, pady=(4, 0))

        self.marco_key = tk.Frame(cfg_modo, bg=C["acento_suave"])
        self.marco_key.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        tk.Label(self.marco_key, text="API Key Gemini:", bg=C["acento_suave"], fg=C["texto"],
                 font=self.f["pequena"]).pack(side="left")
        ttk.Entry(self.marco_key, textvariable=self.var_api_key, width=34, show="•",
                  style="Campo.TEntry", font=self.f["base"]).pack(side="left", padx=8)
        tk.Label(self.marco_key, text="(Clave configurada ✓)", bg=C["acento_suave"],
                 fg=C["ok"], font=self.f["pequena"]).pack(side="left")

        mar_txt = tk.Frame(col_izq, bg=C["tarjeta"])
        mar_txt.grid(row=2, column=0, sticky="nsew", padx=18, pady=(0, 10))
        mar_txt.columnconfigure(0, weight=1)
        mar_txt.rowconfigure(0, weight=1)

        self.txt_enunciado = tk.Text(mar_txt, bg="#F9FBFC", fg=C["texto"], font=self.f["base"],
                                     highlightbackground=C["linea"], highlightthickness=1, wrap="word",
                                     padx=12, pady=10)
        self.txt_enunciado.grid(row=0, column=0, sticky="nsew")
        sb_enunc = ttk.Scrollbar(mar_txt, command=self.txt_enunciado.yview)
        sb_enunc.grid(row=0, column=1, sticky="ns")
        self.txt_enunciado.configure(yscrollcommand=sb_enunc.set)

        ejemplo_defecto = (
            "El tiempo que tarda un sistema informatico en red en ejecutar una instruccion "
            "depende del numero de usuarios conectados a él, si no hay usuarios, el tiempo es 0. "
            "Un estudio arroja los siguientes datos:\n\n"
            "Usuarios: 0, 5, 10, 15, 20, 25\n"
            "Tiempo: 0, 1.2, 4.5, 9.8, 17.1, 26.5\n\n"
            "Halla el tiempo total acumulado en el intervalo analizado."
        )
        self.txt_enunciado.insert("1.0", ejemplo_defecto)

        bot_box = tk.Frame(col_izq, bg=C["tarjeta"])
        bot_box.grid(row=3, column=0, sticky="ew", padx=18, pady=(4, 16))

        self.btn_analizar = Boton(bot_box, "🔍 Analizar Ejercicio con IA", self.ejecutar_analisis_ia,
                                  C["ia_morado"], "#4338CA", fuente=self.f["negrita"], padx=22, pady=10)
        self.btn_analizar.pack(side="left")

        Boton(bot_box, "Borrar", lambda: self.txt_enunciado.delete("1.0", "end"),
              C["tarjeta"], C["linea"], fg=C["apagado"], fuente=self.f["base"], padx=14, pady=10).pack(side="left", padx=(8, 0))

        col_der = self._tarjeta(self.panel_ia)
        col_der.grid(row=0, column=1, sticky="nsew", padx=(9, 18), pady=18)
        col_der.columnconfigure(0, weight=1)
        col_der.rowconfigure(1, weight=1)

        cab_r = tk.Frame(col_der, bg=C["tarjeta"])
        cab_r.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 8))
        tk.Label(cab_r, text="Diagnóstico y Método Sugerido", bg=C["tarjeta"], fg=C["texto"],
                 font=self.f["seccion"]).pack(anchor="w")

        mar_diag = tk.Frame(col_der, bg=C["tarjeta"])
        mar_diag.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 12))
        mar_diag.columnconfigure(0, weight=1)
        mar_diag.rowconfigure(0, weight=1)

        self.txt_diagnostico = tk.Text(mar_diag, bg="white", fg=C["texto"], font=self.f["base"],
                                       relief="flat", wrap="word", padx=14, pady=10, state="disabled")
        self.txt_diagnostico.grid(row=0, column=0, sticky="nsew")
        sb_diag = ttk.Scrollbar(mar_diag, command=self.txt_diagnostico.yview)
        sb_diag.grid(row=0, column=1, sticky="ns")
        self.txt_diagnostico.configure(yscrollcommand=sb_diag.set)

        self.txt_diagnostico.tag_configure("metodo_titulo", font=self.f["titulo"], foreground=C["ia_morado"], spacing3=6)
        self.txt_diagnostico.tag_configure("seccion", font=self.f["negrita"], foreground=C["texto"], spacing1=12, spacing3=4)
        self.txt_diagnostico.tag_configure("cuerpo", font=self.f["base"], foreground=C["texto"], spacing3=4)
        self.txt_diagnostico.tag_configure("orden", font=self.f["negrita"], foreground=C["acento_osc"], spacing3=4)
        self.txt_diagnostico.tag_configure("casilla_nombre", font=self.f["negrita"], foreground=C["acento_osc"])
        self.txt_diagnostico.tag_configure("casilla_valor", font=self.f["mono"], background="#F1F5F9", foreground="#0F172A")
        self.txt_diagnostico.tag_configure("casilla_motivo", font=self.f["pequena"], foreground=C["apagado"], spacing3=6)

        pie_r = tk.Frame(col_der, bg=C["tarjeta"])
        pie_r.grid(row=2, column=0, sticky="ew", padx=18, pady=(6, 16))

        self.btn_cargar_datos = Boton(pie_r, "🚀 Cargar Datos e Ir al Método", self._cargar_datos_en_metodo,
                                      C["ok"], "#08664B", fuente=self.f["negrita"], padx=24, pady=11)
        self.btn_cargar_datos.pack(side="left")

        self.lbl_estado_ia = tk.Label(pie_r, text="Presiona «Analizar Ejercicio» para comenzar.",
                                      bg=C["tarjeta"], fg=C["apagado"], font=self.f["pequena"])
        self.lbl_estado_ia.pack(side="left", padx=14)

    def _actualizar_modo_ia(self):
        if self.var_modo_ia.get() == "gemini":
            self.marco_key.grid()
        else:
            self.marco_key.grid_remove()

    def mostrar_asistente_ia(self):
        self.modo_asistente_activo = True
        self.panel_datos.grid_remove()
        self.panel_resultados.grid_remove()
        self.panel_ia.grid(row=0, column=1, columnspan=2, sticky="nsew")

        for m_id, item in self.items.items():
            item.activar(False)
        self.item_asistente_ia.activar(True)

    def seleccionar_metodo(self, metodo):
        if self.modo_asistente_activo:
            self.modo_asistente_activo = False
            self.panel_ia.grid_remove()
            self.panel_datos.grid()
            self.panel_resultados.grid()
            self.item_asistente_ia.activar(False)

        self.metodo = metodo
        for mid, item in self.items.items():
            item.activar(mid == metodo["id"])
        self.lbl_nombre.configure(text=metodo["nombre"])
        self.lbl_desc.configure(text=metodo["descripcion"])
        self.combo_ej.configure(values=[e["nombre"] for e in metodo["ejemplos"]])
        self.combo_ej.set("Cargar un ejemplo")
        if metodo["tabla"]:
            self.marco_modo.grid()
        else:
            self.marco_modo.grid_remove()
        self._construir_campos()
        self._refrescar_formula()
        self._actualizar_vista()
        self._limpiar_resultado()

    def ejecutar_analisis_ia(self):
        texto = self.txt_enunciado.get("1.0", "end").strip()
        if not texto:
            messagebox.showinfo("Asistente IA", "Por favor ingresa o pega el enunciado de tu ejercicio.")
            return

        self.lbl_estado_ia.configure(text="Conectando con Gemini...", fg=C["ia_morado"])
        self.btn_analizar.configure(text="⏳ Analizando...")

        def tarea():
            try:
                modo = self.var_modo_ia.get()
                api_key = self.var_api_key.get().strip()

                if modo == "gemini" and api_key:
                    try:
                        res = consultar_api_gemini(api_key, texto)
                    except Exception as e:
                        # Respaldo automático al motor heurístico para no interrumpir
                        res = analizar_problema_heuristico(texto)
                        res["justificacion"] = (f"[Aviso de conexión API: {e}\n"
                                                f"Se utilizó el Analizador Heurístico Local con éxito]\n\n"
                                                + res["justificacion"])
                else:
                    res = analizar_problema_heuristico(texto)

                self.after(0, lambda: self._mostrar_diagnostico_ia(res))
            except Exception as e:
                err_msg = str(e)
                self.after(0, lambda: self._mostrar_error_ia(err_msg))

        threading.Thread(target=tarea, daemon=True).start()

    def _mostrar_error_ia(self, error):
        self.btn_analizar.configure(text="🔍 Analizar Ejercicio con IA")
        self.lbl_estado_ia.configure(text="Ocurrió un error en el análisis.", fg=C["error"])
        messagebox.showerror("Error de Análisis", f"No se pudo completar el análisis:\n{error}\n\n"
                                                  "Puedes usar el 'Analizador Local Experto' sin conexión.")

    def _mostrar_diagnostico_ia(self, res):
        self.btn_analizar.configure(text="🔍 Analizar Ejercicio con IA")
        self.lbl_estado_ia.configure(text="¡Análisis completado con éxito!", fg=C["ok"])
        self.resultado_ia_actual = res

        t = self.txt_diagnostico
        t.configure(state="normal")
        t.delete("1.0", "end")

        t.insert("end", f"Método recomendado: {res['nombre']}\n", "metodo_titulo")

        t.insert("end", "📌 ¿Por qué se debe usar este método?\n", "seccion")
        t.insert("end", f"{res['justificacion']}\n\n", "cuerpo")

        t.insert("end", "🎯 Orden y precisión del método:\n", "seccion")
        t.insert("end", f"{res.get('orden_info', 'No aplica')}\n\n", "orden")

        t.insert("end", "📝 Valores que debes ingresar en cada casilla:\n", "seccion")
        for casilla, valor, motivo in res.get("casillas", []):
            t.insert("end", f" • Casilla [{casilla}]: ", "casilla_nombre")
            t.insert("end", f" {valor} \n", "casilla_valor")
            if motivo:
                t.insert("end", f"   ↳ Explicación: {motivo}\n", "casilla_motivo")

        t.insert("end", "\n👉 Haz clic abajo en «Cargar Datos e Ir al Método» para rellenar todo automáticamente y ver la solución.\n", "cuerpo")
        t.configure(state="disabled")

    def _cargar_datos_en_metodo(self):
        if not self.resultado_ia_actual:
            messagebox.showinfo("Asistente", "Primero analiza un problema para obtener los datos a cargar.")
            return

        res = self.resultado_ia_actual
        target_id = res.get("metodo_id", "trapecio")

        metodo_dest = next((m for m in METODOS if m["id"] == target_id), METODOS[0])

        self.seleccionar_metodo(metodo_dest)

        if metodo_dest["tabla"]:
            modo_dest = res.get("modo", "funcion")
            self.modos[metodo_dest["id"]].set(modo_dest)
            self._construir_campos()

        valores = res.get("valores", {})
        for clave, valor in valores.items():
            if clave in self.vars[metodo_dest["id"]]:
                self.vars[metodo_dest["id"]][clave].set(str(valor))

        self._actualizar_vista()
        self.calcular()

        messagebox.showinfo(
            "Datos Cargados con Éxito",
            f"Se ha configurado automáticamente el método:\n«{metodo_dest['nombre']}»\n\n"
            "Todos los campos fueron llenados con los datos del ejercicio analizado por la IA."
        )

    def _cambiar_modo(self, modo):
        self.modos[self.metodo["id"]].set(modo)
        self._construir_campos()

    def _construir_campos(self):
        for w in self.marco_campos.winfo_children():
            w.destroy()
        m = self.metodo
        modo = self.modos[m["id"]].get() if m["tabla"] else "funcion"
        if m["tabla"]:
            if modo == "funcion":
                self.btn_funcion.colorear(C["acento"], C["acento_osc"], "white")
                self.btn_tabla.colorear(C["acento_suave"], C["linea"], C["acento_osc"])
            else:
                self.btn_tabla.colorear(C["acento"], C["acento_osc"], "white")
                self.btn_funcion.colorear(C["acento_suave"], C["linea"], C["acento_osc"])
        fila = 0
        primero = None
        for c in m["campos"]:
            if c["modo"] not in ("ambos", modo):
                continue
            var = self.vars[m["id"]][c["clave"]]
            if c["tipo"] == "check":
                w = tk.Checkbutton(self.marco_campos, text=c["etiqueta"], variable=var, bg=C["tarjeta"],
                                   fg=C["texto"], font=self.f["base"], activebackground=C["tarjeta"],
                                   selectcolor="white", anchor="w", cursor="hand2")
                w.grid(row=fila, column=0, columnspan=2, sticky="w", pady=4)
                w.bind("<FocusIn>", lambda e, t=c["ayuda"]: self.ayuda.set(t))
                w.bind("<Enter>", lambda e, t=c["ayuda"]: self.ayuda.set(t))
            else:
                tk.Label(self.marco_campos, text=c["etiqueta"], bg=C["tarjeta"], fg=C["texto"], font=self.f["base"],
                         anchor="w", width=20).grid(row=fila, column=0, sticky="w", pady=4)
                if c["tipo"] == "combo":
                    w = ttk.Combobox(self.marco_campos, textvariable=var, values=c["valores"], state="readonly",
                                     style="Campo.TCombobox", font=self.f["base"])
                else:
                    w = ttk.Entry(self.marco_campos, textvariable=var, style="Campo.TEntry", font=self.f["base"])
                w.grid(row=fila, column=1, sticky="ew", pady=4)
                w.bind("<FocusIn>", lambda e, t=c["ayuda"]: self.ayuda.set(t))
                if c["tipo"] == "combo" and m.get("formula_por") and m["formula_por"][0] == c["clave"]:
                    w.bind("<<ComboboxSelected>>", self._refrescar_formula)
                if primero is None:
                    primero = (w, c["ayuda"])
            fila += 1
        if primero:
            self.ayuda.set(primero[1])
        self._programar_vista()

    def restablecer(self):
        for c in self.metodo["campos"]:
            self.vars[self.metodo["id"]][c["clave"]].set(c["defecto"])
        self.modos[self.metodo["id"]].set("funcion")
        self.decimales.set("6")
        self._construir_campos()
        self._refrescar_formula()
        self._limpiar_resultado()

    def _aplicar_ejemplo(self, event=None):
        i = self.combo_ej.current()
        if i < 0:
            return
        ej = self.metodo["ejemplos"][i]
        for clave, valor in ej["valores"].items():
            self.vars[self.metodo["id"]][clave].set(valor)
        if self.metodo["tabla"]:
            self.modos[self.metodo["id"]].set(ej.get("modo", "funcion"))
        if "decimales" in ej:
            self.decimales.set(ej["decimales"])
        self._construir_campos()
        self._refrescar_formula()
        self.combo_ej.set("Cargar un ejemplo")
        self.focus_set()
        self.calcular()

    def calcular(self, event=None):
        m = self.metodo
        datos = {clave: var.get() for clave, var in self.vars[m["id"]].items()}
        datos["modo"] = self.modos[m["id"]].get() if m["tabla"] else "funcion"
        try:
            datos["dec"] = max(1, min(12, int(float(self.decimales.get()))))
        except ValueError:
            datos["dec"] = 6
        try:
            resultado = m["funcion"](datos)
        except ErrorMatematico as e:
            self.mostrar_error(str(e))
        except Exception as e:
            self.mostrar_error(f"Ocurrió un error inesperado ({type(e).__name__}: {e}). Revisa los datos escritos.")
        else:
            self.mostrar_resultado(resultado)

    def mostrar_resultado(self, r):
        sub = "  ".join(r.avisos) if r.avisos else "Mira el paso a paso, la tabla y la gráfica en las pestañas de abajo."
        self._pintar_banner("ok", r.etiqueta, r.valor, sub)
        self._escribir_pasos(r.pasos)
        self._llenar_tabla(r.cols, r.filas)
        self.grafica.mostrar(r.grafica)
        self.nb.select(0)

    def mostrar_error(self, mensaje):
        self._pintar_banner("error", "No se puede resolver", "✕", mensaje)
        pasos = Pasos()
        pasos.titulo("Por qué no se pudo resolver")
        pasos.append(("error", mensaje))
        pasos.texto("Corrige el dato indicado y vuelve a presionar Calcular.")
        self._escribir_pasos(pasos)
        self._llenar_tabla([], [])
        self.grafica.mostrar(None)
        self.nb.select(0)

    def _limpiar_resultado(self):
        self._pintar_banner("neutro", "Listo para calcular", "—",
                            "Revisa los datos y presiona Calcular o la tecla Enter.")
        self._escribir_pasos([])
        self._llenar_tabla([], [])
        self.grafica.mostrar(None)

    def _pintar_banner(self, estado, etiqueta, valor, sub):
        fondo, fg, fg_sub = {
            "neutro": (C["tarjeta"], C["texto"], C["apagado"]),
            "ok": (C["ok_suave"], C["ok"], C["texto"]),
            "error": (C["error_suave"], C["error"], C["error"]),
        }[estado]
        for w in (self.banner, self.b_etq, self.b_val, self.b_sub):
            w.configure(bg=fondo)
        self.b_etq.configure(text=etiqueta, fg=fg if estado != "neutro" else C["apagado"])
        self.b_val.configure(text=valor, fg=fg)
        self.b_sub.configure(text=sub, fg=fg_sub)

    def _escribir_pasos(self, pasos):
        t = self.txt
        t.configure(state="normal")
        t.delete("1.0", "end")
        for tipo, contenido in pasos:
            if tipo == "error":
                t.insert("end", contenido + "\n", tipo)
                continue
            for trozo, etiqueta in partir_marcado(contenido):
                t.insert("end", trozo, (tipo, etiqueta) if etiqueta else (tipo,))
            t.insert("end", "\n", tipo)
        t.configure(state="disabled")
        t.yview_moveto(0)

    def _llenar_tabla(self, cols, filas):
        tv = self.tree
        tv.delete(*tv.get_children())
        tv["columns"] = list(cols)
        for c in cols:
            tv.heading(c, text=_enc_bonito(c))
            tv.column(c, width=int(82 * self.k), minwidth=56, anchor="center", stretch=True)
        for i, fila in enumerate(filas[:2000]):
            tv.insert("", "end", values=fila, tags=("par",) if i % 2 else ())
        if len(filas) > 2000:
            tv.insert("", "end", values=["…"] + [f"(se muestran 2000 de {len(filas)} filas)"] + [""] * (len(cols) - 2))


# ======================================================================
# 9. PUNTO DE ENTRADA
# ======================================================================
def main():
    try:
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()


if __name__ == "__main__":
    main()
