"""
Майнкрафт 2D на чистом Python (только стандартная библиотека, tkinter).

Мир 9000 блоков в длину: 10 биомов (равнины, леса, берёзовый лес, пустыня, бесплодные
земли, горы, снежная тундра, тайга, джунгли, саванна), пещеры, руды, деревни с жителями,
день и ночь, мобы, Незер, лук, зачарования, броня, голод.

Управление:
  A / D или стрелки  - ходить   (работает и на русской раскладке: Ф / В)
  W / Пробел / Вверх - прыжок (в творческом режиме полёт; S - вниз)
  ЛКМ (зажать)       - ломать блок / бить моба. С луком в руке: зажми - натяни лук
                       (видна траектория), отпусти - выстрел
  ПКМ                - поставить блок; по верстаку - крафт 3x3, по печи - плавка,
                       по столу зачарований - зачарование, по жителю - торговля
  E                  - инвентарь с крафтом 2x2 и бронёй (Esc - закрыть)
  F / ПКМ с едой     - съесть (голод), ПКМ с бронёй в руке - надеть
  1-9 / колёсико     - выбор ячейки хотбара
  Esc                - пауза: продолжить / СОХРАНИТЬ / выйти в меню

Как попасть в Незер:
  1) добудь обсидиан (глубоко под землёй, нужна алмазная кирка) - нужно 10 блоков;
  2) построй рамку 4x5 (внутри проём 2x3), углы можно не ставить;
  3) сделай огниво (железный слиток + уголь), возьми его в руку и нажми ПКМ внутри рамки;
  4) зайди в портал и постой пару секунд. Незер в 4 раза меньше: 1 блок там = 4 блока здесь.

Лук: палки + нить (нить падает со скелетов, продаёт фермер).
Стрелы: булыжник + палка + листва. Опыт даётся за убийства и руды.
Стол зачарований: книга (3 бумаги, бумага - 3 листвы подряд), 2 алмаза и 4 обсидиана.
"""
import base64
import json
import math
import os
import random
import time
import tkinter as tk
import zlib

TILE = 32
VIEW_W, VIEW_H = 26, 18
CW, CH = VIEW_W * TILE, VIEW_H * TILE
WORLD_W, WORLD_H = 9000, 110        # размеры верхнего мира
NETHER_W = 2250                      # ширина Незера (1 блок Незера = 4 блока мира)
PORTAL_RATIO = 4
SPAWN_X = WORLD_W // 2
BOW_FULL = 30                        # кадров до полной натяжки лука
ARROW_G = 0.010                      # гравитация стрел игрока

DT = 1 / 60
GRAVITY = 0.025
JUMP_V = -0.29
MAX_FALL = 0.6
SPEED = 0.11
PW, PH = 0.7, 1.8          # размеры игрока в блоках
REACH = 5.0                # радиус действия для блоков
ATTACK_R = 4.0             # радиус удара
NEAR_R = 5.0               # радиус действия верстака и печи
MAXHP = 20
DAY_FRAMES = 60 * 720      # сутки = 12 минут (первая ночь примерно через 4-5 минут)
SIM_R = 60                 # радиус симуляции мобов

BIOMES = ["plains", "forest", "desert", "mountain", "birch", "badlands",
          "snowy", "taiga", "jungle", "savanna"]
SLOTS = 3
try:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
except NameError:
    BASE_DIR = os.getcwd()
SAVE_DIR = os.path.join(BASE_DIR, "saves")

# ---------- блоки ----------
(AIR, GRASS, DIRT, STONE, WOOD, LEAVES, PLANKS, COBBLE, TABLE, FURNACE,
 SAND, GLASS, BEDROCK, COAL_ORE, IRON_ORE, GOLD_ORE, DIAMOND_ORE,
 EMERALD_ORE, TRUNK) = range(19)
(SNOW, RED_SAND, TERRACOTTA, CACTUS, BIRCH_TRUNK, SPRUCE_TRUNK, SPRUCE_LEAVES,
 JUNGLE_LEAVES, NETHERRACK, LAVA, GLOWSTONE, QUARTZ_ORE, NETHER_GOLD, OBSIDIAN,
 PORTAL, ENCHANT_TABLE, SOUL_SAND) = range(60, 77)
BLOCKS = set(range(1, 19)) | set(range(60, 77))
# сквозь эти блоки можно ходить (деревья, лава, портал)
PASSABLE = (LEAVES, TRUNK, BIRCH_TRUNK, SPRUCE_TRUNK, SPRUCE_LEAVES, JUNGLE_LEAVES,
            LAVA, PORTAL)

# ---------- предметы ----------
(COAL, IRON_RAW, IRON_INGOT, GOLD_RAW, GOLD_INGOT, DIAMOND, EMERALD, STICK,
 ROTTEN, BONE, GUNPOWDER, RAW_PORK, COOKED_PORK) = range(30, 43)

NAMES = {
    GRASS: "Трава", DIRT: "Земля", STONE: "Камень", WOOD: "Дерево",
    LEAVES: "Листва", PLANKS: "Доски", COBBLE: "Булыжник", TABLE: "Верстак",
    FURNACE: "Печь", SAND: "Песок", GLASS: "Стекло", BEDROCK: "Бедрок",
    COAL_ORE: "Угольная руда", IRON_ORE: "Железная руда",
    GOLD_ORE: "Золотая руда", DIAMOND_ORE: "Алмазная руда",
    EMERALD_ORE: "Изумрудная руда", TRUNK: "Ствол дерева",
    COAL: "Уголь", IRON_RAW: "Сырое железо", IRON_INGOT: "Железный слиток",
    GOLD_RAW: "Сырое золото", GOLD_INGOT: "Золотой слиток", DIAMOND: "Алмаз",
    EMERALD: "Изумруд", STICK: "Палки", ROTTEN: "Гнилая плоть", BONE: "Кость",
    GUNPOWDER: "Порох", RAW_PORK: "Сырая свинина", COOKED_PORK: "Жареная свинина",
}
COLORS = {
    GRASS: "#5aa02c", DIRT: "#8b5a2b", STONE: "#808080", WOOD: "#6b4423",
    LEAVES: "#2e7d32", PLANKS: "#c8963e", COBBLE: "#6e6e6e", TABLE: "#a0652d",
    FURNACE: "#555555", SAND: "#e6d38a", GLASS: "#bfe9f5", BEDROCK: "#1a1a1a",
    COAL_ORE: "#808080", IRON_ORE: "#808080", GOLD_ORE: "#808080",
    DIAMOND_ORE: "#808080", EMERALD_ORE: "#808080", TRUNK: "#6b4423",
    COAL: "#202020", IRON_RAW: "#c9a27a", IRON_INGOT: "#d8d8d8",
    GOLD_RAW: "#d9b94a", GOLD_INGOT: "#f5d33a", DIAMOND: "#4be0e0",
    EMERALD: "#3ddc84", STICK: "#9b7653", ROTTEN: "#7a8f4a", BONE: "#eeeeee",
    GUNPOWDER: "#555566", RAW_PORK: "#e88aa0", COOKED_PORK: "#b5651d",
}
ORE_DOTS = {COAL_ORE: "#151515", IRON_ORE: "#d9b38c", GOLD_ORE: "#f5d33a",
            DIAMOND_ORE: "#4be0e0", EMERALD_ORE: "#3ddc84"}

# ---------- инструменты ----------
# ключ, прилагательное (ж), прилагательное (м), материал, уровень, скорость, урон, цвет
MATS = [
    ("wood", "Деревянная", "Деревянный", PLANKS, 1, 2.0, 4, "#c8963e"),
    ("stone", "Каменная", "Каменный", COBBLE, 2, 4.0, 5, "#9a9a9a"),
    ("iron", "Железная", "Железный", IRON_INGOT, 3, 6.0, 6, "#e6e6e6"),
    ("gold", "Золотая", "Золотой", GOLD_INGOT, 1, 9.0, 4, "#f5d33a"),
    ("diamond", "Алмазная", "Алмазный", DIAMOND, 4, 8.0, 7, "#4be0e0"),
]
# ключ, название, женский род, штук материала, палок
KINDS = [
    ("pickaxe", "кирка", True, 3, 2),
    ("axe", "топор", False, 3, 2),
    ("shovel", "лопата", True, 1, 2),
    ("sword", "меч", False, 2, 1),
]
TOOLS = {}  # id -> (вид, индекс материала)
for _ki, (_kk, _kn, _fem, _mc, _sc) in enumerate(KINDS):
    for _mi, _m in enumerate(MATS):
        _tid = 100 + _ki * 10 + _mi
        NAMES[_tid] = f"{_m[1] if _fem else _m[2]} {_kn}"
        COLORS[_tid] = _m[7]
        TOOLS[_tid] = (_kk, _mi)


def tid(kind, mat):
    ki = [k[0] for k in KINDS].index(kind)
    mi = [m[0] for m in MATS].index(mat)
    return 100 + ki * 10 + mi


# ---------- добыча ----------
DROPS = {TRUNK: WOOD, GRASS: DIRT, STONE: COBBLE, COAL_ORE: COAL, IRON_ORE: IRON_RAW,
         GOLD_ORE: GOLD_RAW, DIAMOND_ORE: DIAMOND, EMERALD_ORE: EMERALD}
# какая кирка по уровню нужна
NEED_TIER = {STONE: 1, COBBLE: 1, COAL_ORE: 1, FURNACE: 1, IRON_ORE: 2,
             GOLD_ORE: 3, DIAMOND_ORE: 3, EMERALD_ORE: 3}
TIER_REQ = {1: "Нужна кирка (деревянная и выше)",
            2: "Нужна каменная кирка или лучше",
            3: "Нужна железная или алмазная кирка"}
# твёрдость (секунды ручной добычи)
HARD = {TRUNK: 2.5, GRASS: 0.6, DIRT: 0.5, SAND: 0.5, WOOD: 2.5, LEAVES: 0.3, PLANKS: 1.8,
        STONE: 2.5, COBBLE: 2.5, TABLE: 1.8, FURNACE: 3.0, GLASS: 0.4,
        COAL_ORE: 3.0, IRON_ORE: 4.0, GOLD_ORE: 4.0, DIAMOND_ORE: 5.0,
        EMERALD_ORE: 5.0}
TOOL_FOR = {TRUNK: "axe", GRASS: "shovel", DIRT: "shovel", SAND: "shovel", WOOD: "axe",
            PLANKS: "axe", TABLE: "axe", STONE: "pickaxe", COBBLE: "pickaxe",
            FURNACE: "pickaxe", COAL_ORE: "pickaxe", IRON_ORE: "pickaxe",
            GOLD_ORE: "pickaxe", DIAMOND_ORE: "pickaxe", EMERALD_ORE: "pickaxe"}

# ---------- еда, броня, прочность ----------
APPLE = 43
NAMES[APPLE] = "Яблоко"
COLORS[APPLE] = "#d32f2f"

# ---------- новые предметы ----------
QUARTZ, PAPER, BOOK, BOW, ARROW, STRING, LIGHTER = range(44, 51)
NAMES.update({
    QUARTZ: "Кварц", PAPER: "Бумага", BOOK: "Книга", BOW: "Лук", ARROW: "Стрела",
    STRING: "Нить", LIGHTER: "Огниво",
    SNOW: "Снег", RED_SAND: "Красный песок", TERRACOTTA: "Терракота", CACTUS: "Кактус",
    BIRCH_TRUNK: "Берёзовый ствол", SPRUCE_TRUNK: "Еловый ствол",
    SPRUCE_LEAVES: "Еловая хвоя", JUNGLE_LEAVES: "Листва джунглей",
    NETHERRACK: "Незерак", LAVA: "Лава", GLOWSTONE: "Светокамень",
    QUARTZ_ORE: "Кварцевая руда", NETHER_GOLD: "Незерское золото",
    OBSIDIAN: "Обсидиан", PORTAL: "Портал", ENCHANT_TABLE: "Стол зачарований",
    SOUL_SAND: "Песок душ",
})
COLORS.update({
    QUARTZ: "#f0ebe3", PAPER: "#f5f5dc", BOOK: "#8b4513", BOW: "#8b5a2b",
    ARROW: "#cfcfcf", STRING: "#eeeeee", LIGHTER: "#b0b0b0",
    SNOW: "#f2f7ff", RED_SAND: "#c4622d", TERRACOTTA: "#9b5a3c", CACTUS: "#3d8b3d",
    BIRCH_TRUNK: "#d8d4c0", SPRUCE_TRUNK: "#4a3320", SPRUCE_LEAVES: "#1f5c3a",
    JUNGLE_LEAVES: "#1f8a2a", NETHERRACK: "#6e2a2a", LAVA: "#ff6a00",
    GLOWSTONE: "#ffd966", QUARTZ_ORE: "#6e2a2a", NETHER_GOLD: "#6e2a2a",
    OBSIDIAN: "#1b1230", PORTAL: "#8a2be2", ENCHANT_TABLE: "#6a1b2a",
    SOUL_SAND: "#4a3b30",
})
ORE_DOTS.update({QUARTZ_ORE: "#f0f0f0", NETHER_GOLD: "#f5d33a"})
DROPS.update({BIRCH_TRUNK: WOOD, SPRUCE_TRUNK: WOOD, SPRUCE_LEAVES: LEAVES,
              JUNGLE_LEAVES: LEAVES, QUARTZ_ORE: QUARTZ, NETHER_GOLD: GOLD_RAW,
              PORTAL: 0})
NEED_TIER.update({QUARTZ_ORE: 1, NETHER_GOLD: 1, OBSIDIAN: 4, ENCHANT_TABLE: 1})
TIER_REQ[4] = "Нужна алмазная кирка"
HARD.update({SNOW: 0.3, RED_SAND: 0.5, TERRACOTTA: 2.0, CACTUS: 0.6, BIRCH_TRUNK: 2.5,
             SPRUCE_TRUNK: 2.5, SPRUCE_LEAVES: 0.3, JUNGLE_LEAVES: 0.3, NETHERRACK: 1.5,
             GLOWSTONE: 0.6, QUARTZ_ORE: 3.0, NETHER_GOLD: 3.0, OBSIDIAN: 40.0,
             PORTAL: 0.3, ENCHANT_TABLE: 3.0, SOUL_SAND: 0.8})
TOOL_FOR.update({BIRCH_TRUNK: "axe", SPRUCE_TRUNK: "axe", SNOW: "shovel",
                 RED_SAND: "shovel", SOUL_SAND: "shovel", TERRACOTTA: "pickaxe",
                 NETHERRACK: "pickaxe", QUARTZ_ORE: "pickaxe", NETHER_GOLD: "pickaxe",
                 OBSIDIAN: "pickaxe", ENCHANT_TABLE: "pickaxe", GLOWSTONE: "pickaxe"})
ORE_XP = {COAL_ORE: 1, IRON_ORE: 2, GOLD_ORE: 2, DIAMOND_ORE: 5, EMERALD_ORE: 5,
          QUARTZ_ORE: 2, NETHER_GOLD: 2}

# ---------- биомы ----------
BIOME_DEFS = {
    "plains": dict(name="Равнины", lo=36, hi=41, vol=0.2, top=GRASS, sub=DIRT, tree="oak", dens=0.04, gap=5),
    "forest": dict(name="Лес", lo=35, hi=42, vol=0.2, top=GRASS, sub=DIRT, tree="oak", dens=0.14, gap=3),
    "birch": dict(name="Берёзовый лес", lo=35, hi=42, vol=0.2, top=GRASS, sub=DIRT, tree="birch", dens=0.12, gap=3),
    "desert": dict(name="Пустыня", lo=37, hi=40, vol=0.15, top=SAND, sub=SAND, tree="cactus", dens=0.025, gap=5),
    "badlands": dict(name="Бесплодные земли", lo=32, hi=42, vol=0.3, top=RED_SAND, sub=TERRACOTTA, tree=None, dens=0, gap=0),
    "mountain": dict(name="Горы", lo=17, hi=31, vol=0.35, top=GRASS, sub=DIRT, tree="spruce", dens=0.02, gap=6),
    "snowy": dict(name="Снежная тундра", lo=36, hi=40, vol=0.2, top=SNOW, sub=DIRT, tree="spruce", dens=0.02, gap=7),
    "taiga": dict(name="Тайга", lo=35, hi=42, vol=0.2, top=GRASS, sub=DIRT, tree="spruce", dens=0.12, gap=3),
    "jungle": dict(name="Джунгли", lo=33, hi=43, vol=0.3, top=GRASS, sub=DIRT, tree="jungle", dens=0.15, gap=4),
    "savanna": dict(name="Саванна", lo=37, hi=42, vol=0.2, top=GRASS, sub=DIRT, tree="acacia", dens=0.03, gap=8),
}
BIOME_WEIGHTS = [("plains", 3), ("forest", 3), ("birch", 2), ("desert", 2), ("badlands", 1),
                 ("mountain", 2), ("snowy", 2), ("taiga", 2), ("jungle", 2), ("savanna", 2)]
PIG_BIOMES = ("plains", "forest", "birch", "taiga", "savanna", "jungle", "snowy")

# ---------- зачарования ----------
ROMAN = {1: "I", 2: "II", 3: "III"}
_TOOLCATS = ("pickaxe", "axe", "shovel")
_ARMORCATS = ("helmet", "chest", "legs", "boots")
ENCHANTS = {
    "efficiency": ("Эффективность", 3, _TOOLCATS),
    "unbreaking": ("Прочность", 3, _TOOLCATS + ("sword", "bow") + _ARMORCATS),
    "silk": ("Шёлковое касание", 1, _TOOLCATS),
    "fortune": ("Удача", 3, _TOOLCATS),
    "sharpness": ("Острота", 3, ("sword",)),
    "knockback": ("Отдача", 2, ("sword",)),
    "power": ("Сила", 3, ("bow",)),
    "infinity": ("Бесконечность", 1, ("bow",)),
    "protection": ("Защита", 3, _ARMORCATS),
    "feather": ("Невесомость", 3, ("boots",)),
}
EXCLUSIVE = [("silk", "fortune")]
ENCH_COSTS = (2, 4, 6)       # сколько уровней опыта стоит каждый вариант

# опыт за убийства
MOB_XP = {"zombie": 5, "skeleton": 5, "creeper": 5, "pig": 2, "pigman": 6, "ghast": 10}


def ench_level(st, key):
    if not st or len(st) < 4 or not st[3]:
        return 0
    return st[3].get(key, 0)


def ench_cat(item):
    if item in TOOLS:
        return TOOLS[item][0]
    if item == BOW:
        return "bow"
    if item in ARMOR:
        return ARMOR_PIECES[ARMOR[item][0]][0]
    return None


def ench_text(key, lvl):
    name, mx, _ = ENCHANTS[key]
    return name if mx == 1 else f"{name} {ROMAN[lvl]}"


def gen_offers(item, seed):
    """Три варианта зачарования (стоимость в уровнях, словарь зачарований)."""
    cat = ench_cat(item)
    if cat is None:
        return []
    rng = random.Random(seed * 1009 + item)
    pool = [k for k, (n, mx, cats) in ENCHANTS.items() if cat in cats]
    offers = []
    for tier, cost in enumerate(ENCH_COSTS, 1):
        chosen = {}
        n_en = 1 + (1 if tier >= 2 and rng.random() < 0.4 else 0)
        for _ in range(n_en):
            k = rng.choice(pool)
            if k in chosen or any(k in e and o in chosen for e in EXCLUSIVE
                                  for o in e if o != k):
                continue
            mx = ENCHANTS[k][1]
            chosen[k] = min(mx, rng.randint(1, tier))
        offers.append((cost, chosen))
    return offers
FOOD = {RAW_PORK: 2, COOKED_PORK: 8, APPLE: 4}   # сколько единиц голода восстанавливает

# ключ, прил. (м), прил. (мн.), материал, защита (шлем, нагрудник, поножи, ботинки),
# прочность (шлем, нагрудник, поножи, ботинки), цвет
ARMOR_MATS = [
    ("iron", "Железный", "Железные", IRON_INGOT, (2, 6, 5, 2), (165, 240, 225, 195), "#d8d8d8"),
    ("gold", "Золотой", "Золотые", GOLD_INGOT, (2, 5, 3, 1), (77, 112, 105, 91), "#f5d33a"),
    ("diamond", "Алмазный", "Алмазные", DIAMOND, (3, 8, 6, 3), (363, 528, 495, 429), "#4be0e0"),
]
ARMOR_PIECES = [("helmet", "шлем", False), ("chest", "нагрудник", False),
                ("legs", "поножи", True), ("boots", "ботинки", True)]
ARMOR_SLOT_NAMES = ["Шлем", "Нагрудник", "Поножи", "Ботинки"]
ARMOR = {}  # id -> (номер части, номер материала)
for _pi, (_pk, _pn, _pl) in enumerate(ARMOR_PIECES):
    for _mi, _m in enumerate(ARMOR_MATS):
        _aid = 200 + _pi * 10 + _mi
        NAMES[_aid] = f"{_m[2] if _pl else _m[1]} {_pn}"
        COLORS[_aid] = _m[6]
        ARMOR[_aid] = (_pi, _mi)

TOOL_DUR = {"wood": 59, "stone": 131, "iron": 250, "gold": 32, "diamond": 1561}


def max_dur(item):
    if item == BOW:
        return 384
    if item == LIGHTER:
        return 64
    if item in TOOLS:
        return TOOL_DUR[MATS[TOOLS[item][1]][0]]
    if item in ARMOR:
        pi, mi = ARMOR[item]
        return ARMOR_MATS[mi][5][pi]
    return None


def stack_limit(item):
    return 1 if max_dur(item) else 64


def make_stack(item, n=1):
    return [item, n, max_dur(item), None]


def fix_stack(st):
    if st is None:
        return None
    st = list(st)
    while len(st) < 4:
        st.append(None)
    return st


PLACEABLE = BLOCKS - {BEDROCK, LAVA, PORTAL}
HB = 9          # ячеек в хотбаре
NSLOTS = 36     # всего ячеек в инвентаре (0-8 хотбар)

# плавка: что -> во что
SMELT = {IRON_RAW: IRON_INGOT, GOLD_RAW: GOLD_INGOT, WOOD: COAL,
         COBBLE: STONE, SAND: GLASS, RAW_PORK: COOKED_PORK}
FUEL_VALUE = {COAL: 8, WOOD: 4, PLANKS: 1, STICK: 1}   # сколько предметов плавит
COOK_TIME = 180   # кадров на один предмет


def new_furnace():
    return {"slots": [None, None, None], "burn": 0, "burn_max": 1, "cook": 0}


# ---------- рецепты (сетка крафта как в Майнкрафте) ----------
GRID_RECIPES = []


def add_recipe(rows, key, out, n=1):
    w = max(len(r) for r in rows)
    pat = [[None if ch == " " else key[ch] for ch in r.ljust(w)] for r in rows]
    GRID_RECIPES.append(dict(pat=pat, out=out, n=n, shapeless=False))


def add_shapeless(items, out, n=1):
    GRID_RECIPES.append(dict(pat=[list(items)], items=sorted(items),
                             out=out, n=n, shapeless=True))


add_shapeless([WOOD], PLANKS, 4)
add_recipe(["P", "P"], {"P": PLANKS}, STICK, 4)
add_recipe(["PP", "PP"], {"P": PLANKS}, TABLE)
add_recipe(["CCC", "C C", "CCC"], {"C": COBBLE}, FURNACE)
for _mi, _m in enumerate(MATS):
    _k = {"M": _m[3], "S": STICK}
    add_recipe(["MMM", " S ", " S "], _k, 100 + _mi)        # кирка
    add_recipe(["MM", "MS", " S"], _k, 110 + _mi)           # топор
    add_recipe(["M", "S", "S"], _k, 120 + _mi)              # лопата
    add_recipe(["M", "M", "S"], _k, 130 + _mi)              # меч
for _mi, _m in enumerate(ARMOR_MATS):
    _k = {"M": _m[3]}
    add_recipe(["MMM", "M M"], _k, 200 + _mi)               # шлем
    add_recipe(["M M", "MMM", "MMM"], _k, 210 + _mi)        # нагрудник
    add_recipe(["MMM", "M M", "M M"], _k, 220 + _mi)        # поножи
    add_recipe(["M M", "M M"], _k, 230 + _mi)               # ботинки
add_recipe(["LLL"], {"L": LEAVES}, PAPER, 3)
add_shapeless([PAPER, PAPER, PAPER], BOOK)
add_shapeless([IRON_INGOT, COAL], LIGHTER)
add_recipe([" B ", "DOD", "OOO"], {"B": BOOK, "D": DIAMOND, "O": OBSIDIAN}, ENCHANT_TABLE)
add_recipe([" ST", "S T", " ST"], {"S": STICK, "T": STRING}, BOW)
add_recipe(["C", "S", "L"], {"C": COBBLE, "S": STICK, "L": LEAVES}, ARROW, 4)


def match_recipe(cells, w, h):
    """cells - список предметов (или None) размером w*h. Возвращает (предмет, кол-во)."""
    rows = [cells[r * w:(r + 1) * w] for r in range(h)]
    pts = [(r, c) for r in range(h) for c in range(w) if rows[r][c] is not None]
    if not pts:
        return None
    r0 = min(p[0] for p in pts)
    r1 = max(p[0] for p in pts)
    c0 = min(p[1] for p in pts)
    c1 = max(p[1] for p in pts)
    pat = [row[c0:c1 + 1] for row in rows[r0:r1 + 1]]
    flat = sorted(x for row in pat for x in row if x is not None)
    for rec in GRID_RECIPES:
        if rec["shapeless"]:
            if flat == rec["items"]:
                return rec["out"], rec["n"]
            continue
        rp = rec["pat"]
        if len(rp) != len(pat) or len(rp[0]) != len(pat[0]):
            continue
        if rp == pat or [r[::-1] for r in rp] == pat:
            return rec["out"], rec["n"]
    return None


# ---------- режимы игры ----------
MODES = [
    ("creative", "Творческий", "Бесконечные блоки, полёт (W/Пробел вверх, S вниз), без урона и голода"),
    ("peaceful", "Мирный", "Враги не появляются, голод не тратится, здоровье быстро лечится"),
    ("normal", "Нормальный", "Враги, голод и броня - как в обычном выживании"),
    ("hardcore", "Хардкор", "Урон x1.5 и одна жизнь: после смерти мир удаляется навсегда"),
]
MODE_NAMES = {m[0]: m[1] for m in MODES}
DMG_MULT = {"creative": 0.0, "peaceful": 1.0, "normal": 1.0, "hardcore": 1.5}
CREATIVE_ITEMS = (sorted(BLOCKS - {BEDROCK, LAVA, PORTAL}) + list(range(30, 51))
                  + sorted(TOOLS) + sorted(ARMOR))

# размеры интерфейса инвентаря
SL = 42
UI_W, UI_H = 460, 410
UI_X, UI_Y = (CW - UI_W) // 2, 40

# ---------- жители и торговля: (отдать, (получить, сколько)) ----------
PROFS = {
    "farmer": ("Фермер", "#7cb342", [
        ({RAW_PORK: 3}, (EMERALD, 1)),
        ({WOOD: 6}, (EMERALD, 1)),
        ({EMERALD: 1}, (COOKED_PORK, 3)),
        ({EMERALD: 2}, (GOLD_INGOT, 1)),
    ]),
    "blacksmith": ("Кузнец", "#546e7a", [
        ({COAL: 15}, (EMERALD, 1)),
        ({IRON_INGOT: 4}, (EMERALD, 1)),
        ({DIAMOND: 1}, (EMERALD, 4)),
        ({EMERALD: 3}, (tid("sword", "iron"), 1)),
        ({EMERALD: 5}, (tid("pickaxe", "iron"), 1)),
        ({EMERALD: 10}, (tid("sword", "diamond"), 1)),
        ({EMERALD: 14}, (tid("pickaxe", "diamond"), 1)),
    ]),
    "cleric": ("Священник", "#8e24aa", [
        ({ROTTEN: 8}, (EMERALD, 1)),
        ({BONE: 6}, (EMERALD, 1)),
        ({GUNPOWDER: 3}, (EMERALD, 2)),
        ({GOLD_INGOT: 3}, (EMERALD, 2)),
        ({EMERALD: 1}, (GOLD_INGOT, 1)),
    ]),
    "mason": ("Каменщик", "#bcaaa4", [
        ({COBBLE: 16}, (EMERALD, 1)),
        ({SAND: 12}, (EMERALD, 1)),
        ({EMERALD: 1}, (GLASS, 6)),
        ({EMERALD: 1}, (FURNACE, 1)),
        ({EMERALD: 2}, (tid("axe", "stone"), 1)),
    ]),
}

PROFS["farmer"][2].append(({EMERALD: 1}, (STRING, 3)))
PROFS["blacksmith"][2].append(({EMERALD: 1}, (ARROW, 8)))
PROFS["blacksmith"][2].append(({EMERALD: 3}, (BOW, 1)))
PROFS["cleric"][2].append(({EMERALD: 2}, (BOOK, 1)))
PROFS["cleric"][2].append(({EMERALD: 3}, (LIGHTER, 1)))

# ---------- мобы ----------
MOBS = {
    "zombie": dict(w=0.7, h=1.8, hp=20, speed=0.045, hostile=True),
    "skeleton": dict(w=0.7, h=1.8, hp=20, speed=0.035, hostile=True),
    "creeper": dict(w=0.7, h=1.6, hp=20, speed=0.05, hostile=True),
    "pig": dict(w=0.9, h=0.8, hp=10, speed=0.03, hostile=False),
    "villager": dict(w=0.7, h=1.8, hp=20, speed=0.025, hostile=False),
}
MOBS["pigman"] = dict(w=0.7, h=1.8, hp=20, speed=0.04, hostile=True)
MOBS["ghast"] = dict(w=1.8, h=1.8, hp=10, speed=0.02, hostile=True, fly=True)
HOSTILES = ("zombie", "skeleton", "creeper", "pigman", "ghast")
ENT_COLORS = {
    "zombie": ("#2f6f8f", "#5c9c4a"), "skeleton": ("#cfcfcf", "#ececec"),
    "creeper": ("#4caf50", "#66bb6a"), "pig": ("#f4a6b8", "#f4a6b8"),
    "villager": ("#888888", "#e8c39e"),
    "pigman": ("#a8506a", "#c8788a"), "ghast": ("#f2f2f2", "#f2f2f2"),
}
MOB_DROPS = {"zombie": [(ROTTEN, 0, 2)],
             "skeleton": [(BONE, 0, 2), (ARROW, 0, 2), (STRING, 0, 1)],
             "creeper": [(GUNPOWDER, 0, 2)], "pig": [(RAW_PORK, 1, 3)],
             "pigman": [(ROTTEN, 0, 1), (GOLD_RAW, 0, 1)],
             "ghast": [(GUNPOWDER, 0, 2)]}

KEYMAP = {
    "a": "left", "left": "left", "cyrillic_ef": "left",
    "d": "right", "right": "right", "cyrillic_ve": "right",
    "w": "jump", "up": "jump", "space": "jump", "cyrillic_tse": "jump",
    "s": "down", "down": "down", "cyrillic_yeru": "down",
}

CRACKS = [((16, 16), (8, 4)), ((16, 16), (26, 8)), ((16, 16), (28, 24)),
          ((16, 16), (6, 26)), ((8, 4), (2, 10)), ((26, 8), (30, 2)),
          ((28, 24), (22, 30)), ((6, 26), (12, 31))]

_shade_cache = {}


def shade(color, lvl):
    """Затемнение цвета для ночи (lvl 0..6)."""
    if lvl <= 0:
        return color
    key = (color, lvl)
    res = _shade_cache.get(key)
    if res is None:
        f = 1 - 0.6 * lvl / 6
        r = int(int(color[1:3], 16) * f)
        g = int(int(color[3:5], 16) * f)
        b = int(int(color[5:7], 16) * f)
        res = "#%02x%02x%02x" % (r, g, b)
        _shade_cache[key] = res
    return res


class Ent:
    def __init__(self, kind, x, y, prof=None):
        spec = MOBS[kind]
        self.kind = kind
        self.x, self.y = x, y
        self.w, self.h = spec["w"], spec["h"]
        self.hp = self.maxhp = spec["hp"]
        self.vx = self.vy = 0.0
        self.on_ground = False
        self.blocked = False
        self.face = random.choice([-1, 1])
        self.dir = 0
        self.timer = random.randint(20, 120)
        self.cool = random.randint(30, 90)
        self.fuse = 0
        self.kb = 0
        self.hurt = 0
        self.home = x
        self.prof = prof
        self.nodrop = False
        self.angry = False


class Game:
    def __init__(self, root):
        self.root = root
        root.title("Майнкрафт 2D")
        root.resizable(False, False)
        self.canvas = tk.Canvas(root, width=CW, height=CH,
                                bg="#87ceeb", highlightthickness=0)
        self.canvas.pack()

        self.keys = set()
        self.mouse = (0, 0)
        self.buttons = set()
        self.selected = 0
        self.hitboxes = []

        root.bind("<KeyPress>", self.on_key_press)
        root.bind("<KeyRelease>", self.on_key_release)
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<B3-Motion>", self.on_motion)
        self.canvas.bind("<ButtonPress-1>", lambda e: self.on_button(e, 1, True))
        self.canvas.bind("<ButtonRelease-1>", lambda e: self.on_button(e, 1, False))
        self.canvas.bind("<ButtonPress-3>", lambda e: self.on_button(e, 3, True))
        self.canvas.bind("<ButtonRelease-3>", lambda e: self.on_button(e, 3, False))
        self.canvas.bind("<MouseWheel>", lambda e: self.wheel(-1 if e.delta > 0 else 1))
        self.canvas.bind("<Button-4>", lambda e: self.wheel(-1))
        self.canvas.bind("<Button-5>", lambda e: self.wheel(1))

        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.scene = "title"       # title / slots / play
        self.paused = False
        self.dead = False
        self.cause = ""
        self.autosave_t = 0
        self.slot = None
        self.world = None
        self.anim = 0
        self.save_msg = ""
        self.confirm_del = None
        self.create_slot = None
        self.cname = ""
        self.cseed = ""
        self.cmode = 2
        self.cfocus = "name"
        self.mode = "normal"
        self.name = ""
        self.ui = None
        self.ui_data = None
        self.ui_slots = []
        self.cursor = None
        self.grid = []
        self.grid_w = 2
        self.book_prev = "inv"
        self.pal_items = CREATIVE_ITEMS
        self.scroll_off = 0
        self.furnaces = {}
        self.slots = [None] * NSLOTS
        self.armor = [None] * 4
        self.W = WORLD_W
        self.dim = "over"
        self.dims = {}
        self.xp_level = 0
        self.xp_prog = 0
        self.ench_slot = [None]
        self.ench_seed = 1
        self.charge = 0
        self.portal_t = 0
        self.portal_lock = False
        self.lava_t = 0
        self.splash = random.choice(["Теперь с жителями!", "Алмазы глубже!",
                                     "Бойся криперов!", "Торгуй изумрудами!",
                                     "Всё на чистом Python!"])
        self.metas = self.read_metas()
        self.acc = 0.0
        self.last = time.perf_counter()
        self.loop()

    # =====================================================================
    # генерация мира
    # =====================================================================
    def progress(self, text):
        self.canvas.delete("all")
        self.canvas.configure(bg="#2b2b33")
        self.canvas.create_text(CW // 2, CH // 2, fill="white", font=("Arial", 22, "bold"),
                                text=text)
        self.root.update()

    def new_world(self, seed=None):
        random.seed(seed)
        W, H = WORLD_W, WORLD_H
        self.W = W
        k = W / 1200.0
        self.progress("Генерация мира: биомы и рельеф...")

        # биомы
        names = [b for b, w in BIOME_WEIGHTS for _ in range(w)]
        biome = [None] * W
        x = 0
        prev = None
        while x < W:
            length = random.randint(110, 260)
            b = random.choice(names)
            for _ in range(6):
                if b != prev:
                    break
                b = random.choice(names)
            prev = b
            for i in range(x, min(W, x + length)):
                biome[i] = b
            x += length
        villages = []
        for kk in range(-15, 16):
            vx = SPAWN_X + 40 + kk * 290 + random.randint(-15, 15)
            if 60 <= vx <= W - 160:
                villages.append(vx)
        for vx in villages:
            for i in range(max(0, vx - 12), min(W, vx + 58)):
                biome[i] = "plains"
        for i in range(SPAWN_X - 60, SPAWN_X + 60):
            biome[i] = "plains"
        self.biome = biome

        # высоты
        h = 38
        heights = []
        for x in range(W):
            d = BIOME_DEFS[biome[x]]
            p = d["vol"]
            r = random.random()
            if r < p:
                h -= 1
            elif r > 1 - p:
                h += 1
            if h < d["lo"]:
                h += 1
            elif h > d["hi"]:
                h -= 1
            heights.append(h)

        # ровные площадки под деревни
        pinned = [False] * W
        spans = []
        for vi, vx in enumerate(villages):
            n = random.randint(3, 4)
            x0, x1 = vx - 3, vx + 10 * n + 3
            base = max(36, min(41, heights[vx]))
            for x in range(x0, x1 + 1):
                heights[x] = base
                pinned[x] = True
            spans.append((vi, vx, n, base, x0, x1))
        for x in range(1, W):
            if not pinned[x]:
                heights[x] = max(heights[x - 1] - 1, min(heights[x - 1] + 1, heights[x]))
        for x in range(W - 2, -1, -1):
            if not pinned[x]:
                heights[x] = max(heights[x + 1] - 1, min(heights[x + 1] + 1, heights[x]))
        self.top = heights
        self.village_spans = [(sp[4], sp[5]) for sp in spans]

        # столбцы -> строки
        cols = []
        for x in range(W):
            top, bn = heights[x], biome[x]
            d = BIOME_DEFS[bn]
            n = H - top
            if bn == "desert":
                body = bytes([SAND]) * 5 + bytes([STONE]) * (n - 5)
            elif bn == "badlands":
                layers = [RED_SAND] + [TERRACOTTA if (i // 2) % 2 == 0 else RED_SAND
                                       for i in range(1, 12)]
                body = bytes(layers) + bytes([STONE]) * (n - len(layers))
            elif bn == "mountain":
                if top < 22:
                    body = bytes([SNOW]) + bytes([STONE]) * (n - 1)
                elif top < 27:
                    body = bytes([STONE]) * n
                else:
                    body = bytes([GRASS]) + bytes([DIRT]) * 3 + bytes([STONE]) * (n - 4)
            else:
                body = bytes([d["top"]]) + bytes([d["sub"]]) * 3 + bytes([STONE]) * (n - 4)
            col = bytearray(top) + bytearray(body)
            col[H - 1] = BEDROCK
            if random.random() < 0.5:
                col[H - 2] = BEDROCK
            cols.append(col)
        self.world = [bytearray(r) for r in zip(*cols)]
        world = self.world
        del cols

        # руды
        self.progress("Генерация мира: руды...")
        self.gen_vein(COAL_ORE, int(1800 * k), (4, 9), 5, 70)
        self.gen_vein(IRON_ORE, int(1200 * k), (3, 7), 12, 70)
        self.gen_vein(GOLD_ORE, int(450 * k), (2, 5), 28, 70)
        self.gen_vein(DIAMOND_ORE, int(260 * k), (1, 4), 42, 75)
        self.gen_vein(EMERALD_ORE, int(150 * k), (1, 2), 20, 70)
        self.gen_vein(OBSIDIAN, int(25 * k), (2, 5), 42, 75)

        # пещеры
        self.progress("Генерация мира: пещеры...")
        offs = {1: [(dx, dy) for dx in range(-1, 2) for dy in range(-1, 2) if dx * dx + dy * dy <= 1],
                2: [(dx, dy) for dx in range(-2, 3) for dy in range(-2, 3) if dx * dx + dy * dy <= 4]}
        for _ in range(int(450 * k)):
            x = random.randint(5, W - 6)
            y = random.randint(heights[x] + 8, H - 8)
            for _ in range(random.randint(30, 90)):
                for dx, dy in offs[random.choice((1, 1, 2))]:
                    tx, ty = x + dx, y + dy
                    if 0 < tx < W - 1 and heights[tx] + 6 < ty < H - 3:
                        world[ty][tx] = AIR
                x = max(2, min(W - 3, x + random.choice((-1, 0, 1))))
                y = max(10, min(H - 5, y + random.choice((-1, 0, 1))))

        # деревья, кактусы
        self.progress("Генерация мира: растительность...")
        banned = bytearray(W)
        for a, b in self.village_spans:
            for xx in range(max(0, a - 2), min(W, b + 3)):
                banned[xx] = 1
        last = -10
        for x in range(6, W - 6):
            if banned[x]:
                continue
            d = BIOME_DEFS[biome[x]]
            if d["tree"] is None:
                continue
            if random.random() < d["dens"] and x - last > d["gap"]:
                if self.plant(x, d["tree"], heights[x]):
                    last = x

        # деревни и жители
        self.progress("Генерация мира: деревни...")
        self.ents = []
        for vi, vx, n, base, x0, x1 in spans:
            self.build_village(vi, vx, n, base)

        # свиньи
        for _ in range(int(70 * k)):
            x = random.randint(5, W - 6)
            if biome[x] in PIG_BIOMES and not banned[x]:
                self.ents.append(Ent("pig", x + 0.05, heights[x] - 0.8 - 0.01))

        # игрок (расчищаем место под спавн)
        self.spawn_ground = heights[SPAWN_X]
        self.px = SPAWN_X + 0.15
        self.py = self.spawn_ground - PH - 0.01
        self.clear_spawn()
        self.init_state()
        self.say("Руби деревья (ЛКМ), нажми E - крафт. Деревня справа от тебя!", 360)

    def plant(self, x, kind, top):
        w = self.world
        base = top - 1
        ground = w[top][x]
        if kind == "cactus":
            if ground != SAND:
                return False
            for i in range(random.randint(1, 3)):
                w[base - i][x] = CACTUS
            return True
        if ground not in (GRASS, DIRT, SNOW, STONE) or ground == STONE and kind != "spruce":
            return False
        if kind in ("oak", "birch"):
            trunk = random.randint(4, 6) if kind == "oak" else random.randint(5, 7)
            tb = TRUNK if kind == "oak" else BIRCH_TRUNK
            for i in range(trunk):
                w[base - i][x] = tb
            t = base - trunk + 1
            for dy in range(-2, 2):
                for dx in range(-2, 3):
                    if abs(dx) == 2 and dy in (-2, 1):
                        continue
                    if w[t + dy][x + dx] == AIR:
                        w[t + dy][x + dx] = LEAVES
        elif kind == "spruce":
            t = random.randint(6, 9)
            for i in range(t):
                w[base - i][x] = SPRUCE_TRUNK
            apex = base - t
            for kk in range(0, t - 1):
                y = apex + kk
                hw = min(3, (kk + 1) // 2)
                for dx in range(-hw, hw + 1):
                    if w[y][x + dx] == AIR:
                        w[y][x + dx] = SPRUCE_LEAVES
        elif kind == "jungle":
            t = random.randint(9, 13)
            for i in range(t):
                w[base - i][x] = TRUNK
            tp = base - t + 1
            for dy, r in ((-1, 2), (0, 3), (1, 3), (2, 2)):
                for dx in range(-r, r + 1):
                    if w[tp + dy][x + dx] == AIR:
                        w[tp + dy][x + dx] = JUNGLE_LEAVES
        else:   # acacia
            t = random.randint(5, 6)
            for i in range(t):
                w[base - i][x] = TRUNK
            tp = base - t + 1
            for dx in range(-3, 4):
                if w[tp][x + dx] == AIR:
                    w[tp][x + dx] = LEAVES
            for dx in range(-2, 3):
                if w[tp - 1][x + dx] == AIR:
                    w[tp - 1][x + dx] = LEAVES
        return True

    def gen_nether(self):
        """Создаёт Незер: огромная пещера с лавой, островами, светокамнем и рудами."""
        W, H = NETHER_W, WORLD_H
        self.progress("Генерация Незера...")
        ph = [random.uniform(0, 6.28) for _ in range(3)]
        ceil = []
        c = 20
        for x in range(W):
            c += random.choice((-1, 0, 0, 1))
            c = max(12, min(30, c))
            ceil.append(c)
        floor = [int(round(88 + 9 * math.sin(x * 0.011 + ph[0]) + 5 * math.sin(x * 0.037 + ph[1])
                           + 2 * math.sin(x * 0.13 + ph[2]))) for x in range(W)]
        for x in range(1, W):
            floor[x] = max(floor[x - 1] - 1, min(floor[x - 1] + 1, floor[x]))
        for x in range(W - 2, -1, -1):
            floor[x] = max(floor[x + 1] - 1, min(floor[x + 1] + 1, floor[x]))
        LAVA_Y = 94
        cols = []
        for x in range(W):
            cy = ceil[x]
            fy = max(cy + 15, min(H - 5, floor[x]))
            col = bytearray(H)
            col[:cy] = bytes([NETHERRACK]) * cy
            col[fy:] = bytes([NETHERRACK]) * (H - fy)
            if fy > LAVA_Y:
                col[LAVA_Y:fy] = bytes([LAVA]) * (fy - LAVA_Y)
            col[:3] = bytes([BEDROCK]) * 3
            col[H - 3:] = bytes([BEDROCK]) * 3
            cols.append(col)
        world = [bytearray(r) for r in zip(*cols)]
        del cols

        def setc(x, y, b, only=(AIR,)):
            if 0 <= x < W and 3 <= y < H - 3 and world[y][x] in only:
                world[y][x] = b

        # парящие острова
        for _ in range(W // 40):
            cx = random.randint(5, W - 6)
            cyy = random.randint(ceil[cx] + 10, 72)
            rx, ry = random.randint(3, 9), random.randint(1, 3)
            for dx in range(-rx, rx + 1):
                for dy in range(-ry, ry + 1):
                    if (dx / rx) ** 2 + (dy / ry) ** 2 <= 1:
                        setc(cx + dx, cyy + dy, NETHERRACK)
        # сталактиты и сталагмиты
        for _ in range(W // 5):
            x = random.randint(1, W - 2)
            for i in range(random.randint(2, 9)):
                setc(x, ceil[x] + i, NETHERRACK)
        for _ in range(W // 8):
            x = random.randint(1, W - 2)
            if floor[x] < LAVA_Y:
                for i in range(1, random.randint(2, 6) + 1):
                    setc(x, floor[x] - i, NETHERRACK)
        # светокамень на потолке
        for _ in range(W // 25):
            x = random.randint(3, W - 4)
            for dy in range(-1, 3):
                for dx in range(-2, 3):
                    if random.random() < 0.6:
                        setc(x + dx, ceil[x] + dy, GLOWSTONE, (AIR, NETHERRACK))
        # песок душ
        for _ in range(W // 30):
            x = random.randint(3, W - 12)
            for xx in range(x, x + random.randint(3, 8)):
                if floor[xx] < LAVA_Y:
                    setc(xx, floor[xx], SOUL_SAND, (NETHERRACK,))
        # руды
        for ore, cnt, size in ((QUARTZ_ORE, W // 4, (3, 8)), (NETHER_GOLD, W // 10, (2, 5))):
            for _ in range(cnt):
                x = random.randint(1, W - 2)
                y = random.randint(4, H - 5)
                for _ in range(random.randint(*size)):
                    setc(x, y, ore, (NETHERRACK,))
                    x += random.choice((-1, 0, 1))
                    y += random.choice((-1, 0, 1))
        return dict(world=world, top=ceil, biome=["nether"] * W, village_spans=[],
                    ents=[], furnaces={}, arrows=[], W=W)

    def init_state(self):
        self.vx = self.vy = 0.0
        self.kbx = 0.0
        self.on_ground = False
        self.fall_top = None
        self.slots = [None] * NSLOTS
        self.armor = [None] * 4
        self.selected = 0
        self.cursor = None
        self.grid = []
        self.furnaces = {}
        self.hp = MAXHP
        self.food = 20.0
        self.exh = 0.0
        self.inv_t = 0
        self.regen = 0
        self.ui = None
        self.ui_data = None
        self.scroll_off = 0
        self.mining = None
        self.atk = 0
        self.pcool = 0
        self.arrows = []
        self.spawn_t = 120
        self.time = int(DAY_FRAMES * 0.15)
        self.light = 1.0
        self.msg = ""
        self.msg_t = 0
        self.dead = False
        self.cause = ""
        self.autosave_t = 60 * 120
        self.dim = "over"
        self.dims = {}
        self.xp_level = 0
        self.xp_prog = 0
        self.ench_slot = [None]
        self.ench_seed = 1
        self.charge = 0
        self.portal_t = 0
        self.portal_lock = False
        self.lava_t = 0

    def clear_spawn(self):
        g = self.spawn_ground
        for xx in (SPAWN_X - 1, SPAWN_X, SPAWN_X + 1):
            for yy in range(g - 6, g):
                self.world[yy][xx] = AIR
            if self.world[g][xx] == AIR:
                self.world[g][xx] = GRASS

    def gen_vein(self, ore, count, size, off_min, off_max):
        W, H = WORLD_W, WORLD_H
        world = self.world
        top = self.top
        for _ in range(count):
            x = random.randint(1, W - 2)
            y = random.randint(top[x] + off_min, min(H - 3, top[x] + off_max))
            for _ in range(random.randint(*size)):
                if 0 <= x < W and 0 <= y < H - 2 and world[y][x] == STONE:
                    world[y][x] = ore
                x += random.choice((-1, 0, 1))
                y += random.choice((-1, 0, 1))

    def build_village(self, vi, vx, n, base):
        profs = list(PROFS.keys())
        if vi == 0:
            profs = ["blacksmith", "farmer", "cleric", "mason"]
        else:
            random.shuffle(profs)
        for i in range(n):
            x0 = vx + i * 10
            self.build_house(x0, base, table=(i % 2 == 0), furnace=(i % 2 == 1))
            self.add_villager(x0 + 3, base, profs[i % len(profs)])
            if random.random() < 0.5:
                self.add_villager(x0 + 8, base, random.choice(profs))

    def build_house(self, x0, g, table, furnace):
        w = self.world
        for y in range(g - 9, g):
            for x in range(x0 - 1, x0 + 8):
                w[y][x] = AIR
        for x in range(x0, x0 + 7):
            w[g][x] = PLANKS
        for y in (g - 1, g - 2, g - 3):
            w[y][x0] = WOOD
            w[y][x0 + 6] = WOOD
        for xx in (x0, x0 + 6):     # двери с обеих сторон
            w[g - 1][xx] = AIR
            w[g - 2][xx] = AIR
        for x in range(x0, x0 + 7):
            w[g - 4][x] = PLANKS
        for x in range(x0 + 1, x0 + 6):
            w[g - 5][x] = PLANKS
        w[g - 4][x0 + 3] = GLASS    # окошко в крыше
        for x in range(x0 + 2, x0 + 5):
            w[g - 6][x] = PLANKS
        if table:
            w[g - 1][x0 + 2] = TABLE
        if furnace:
            w[g - 1][x0 + 4] = FURNACE

    def add_villager(self, x, ground, prof):
        self.ents.append(Ent("villager", x + 0.15, ground - 1.8 - 0.01, prof))

    # =====================================================================
    # мир и физика
    # =====================================================================
    def get(self, x, y):
        if x < 0 or x >= self.W or y >= WORLD_H:
            return STONE
        if y < 0:
            return AIR
        return self.world[y][x]

    def collides(self, x, y, w=PW, h=PH):
        for ty in range(math.floor(y), math.floor(y + h - 1e-9) + 1):
            for tx in range(math.floor(x), math.floor(x + w - 1e-9) + 1):
                b = self.get(tx, ty)
                if b != AIR and b not in PASSABLE:
                    return True
        return False

    def move(self, e):
        if not MOBS[e.kind].get("fly"):
            e.vy = min(e.vy + GRAVITY, MAX_FALL)
        e.x += e.vx
        e.blocked = False
        if self.collides(e.x, e.y, e.w, e.h):
            if e.vx > 0:
                e.x = math.floor(e.x + e.w) - e.w - 0.001
            elif e.vx < 0:
                e.x = math.floor(e.x) + 1.001
            e.blocked = True
        e.y += e.vy
        e.on_ground = False
        if self.collides(e.x, e.y, e.w, e.h):
            if e.vy > 0:
                e.y = math.floor(e.y + e.h) - e.h - 0.001
                e.on_ground = True
            elif e.vy < 0:
                e.y = math.floor(e.y) + 1.001
            e.vy = 0

    def covered(self, x, y):
        """Есть ли над клеткой (x, y) какой-нибудь блок (не видно неба)."""
        if x < 0 or x >= self.W:
            return True
        for yy in range(0, max(0, y)):
            if self.world[yy][x] != AIR:
                return True
        return False

    # =====================================================================
    # инвентарь
    # =====================================================================
    @property
    def menu_open(self):
        return self.ui is not None

    # =====================================================================
    # инвентарь: ячейки со стопками [предмет, количество, прочность]
    # =====================================================================
    def have(self, item):
        return sum(s[1] for s in self.slots if s and s[0] == item)

    def can_add(self, item, n=1):
        lim = stack_limit(item)
        room = 0
        for s in self.slots:
            if s is None:
                room += lim
            elif s[0] == item and lim > 1:
                room += lim - s[1]
            if room >= n:
                return True
        return False

    def add(self, item, n=1):
        """Положить предмет в инвентарь. Возвращает, сколько не поместилось."""
        lim = stack_limit(item)
        if lim > 1:
            for s in self.slots:
                if n > 0 and s and s[0] == item and s[1] < lim:
                    put = min(n, lim - s[1])
                    s[1] += put
                    n -= put
        for i, s in enumerate(self.slots):
            if n <= 0:
                break
            if s is None:
                put = min(n, lim)
                self.slots[i] = make_stack(item, put)
                n -= put
        return n

    def take(self, item, n):
        for i in range(len(self.slots) - 1, -1, -1):
            s = self.slots[i]
            if n > 0 and s and s[0] == item:
                t = min(n, s[1])
                s[1] -= t
                n -= t
                if s[1] <= 0:
                    self.slots[i] = None

    def add_stack(self, st):
        if st[2] is None:
            self.add(st[0], st[1])
            return
        for i, s in enumerate(self.slots):
            if s is None:
                self.slots[i] = st
                return

    def best_tool(self, kind, need=0):
        """Лучший инструмент вида kind (уровень не ниже need):
        (скорость или урон, уровень, номер ячейки)."""
        best = None
        for i, s in enumerate(self.slots):
            if s and s[0] in TOOLS:
                kk, mi = TOOLS[s[0]]
                m = MATS[mi]
                if kk == kind and m[4] >= need:
                    if kind == "sword":
                        val = m[6]
                    else:
                        val = m[5] * (1 + 0.3 * ench_level(s, "efficiency"))
                    if best is None or val > best[0]:
                        best = (val, m[4], i)
        return best

    def wear_tool(self, idx):
        s = self.slots[idx]
        if self.mode == "creative" or not s:
            return
        if s[0] not in TOOLS and s[0] not in (BOW, LIGHTER):
            return
        lvl = ench_level(s, "unbreaking")
        if lvl and random.random() < lvl / (lvl + 1.0):
            return
        s[2] -= 1
        if s[2] <= 0:
            self.slots[idx] = None
            self.say(f"Сломалось: {NAMES[s[0]]}", 120)

    def mine_time(self, b):
        """(кадров, ячейка инструмента) или None, если без нужной кирки блок не сломать."""
        if self.mode == "creative":
            return 4, None
        need = NEED_TIER.get(b, 0)
        kind = TOOL_FOR.get(b)
        speed = 1.0
        idx = None
        if kind:
            bt = self.best_tool(kind, need)
            if need > 0 and bt is None:
                return None
            if bt:
                speed = bt[0]
                idx = bt[2]
        return max(6, HARD[b] * 60 / speed), idx

    # =====================================================================
    # броня и голод
    # =====================================================================
    def xp_need(self, level):
        return 6 + 3 * level

    def add_xp(self, n):
        if n <= 0 or self.mode == "creative":
            return
        self.xp_prog += n
        while self.xp_prog >= self.xp_need(self.xp_level):
            self.xp_prog -= self.xp_need(self.xp_level)
            self.xp_level += 1
            self.say(f"Уровень опыта: {self.xp_level}!", 90)

    def armor_points(self):
        total = 0
        for st in self.armor:
            if st:
                pi, mi = ARMOR[st[0]]
                total += ARMOR_MATS[mi][4][pi] + ench_level(st, "protection")
        return min(20, total)

    def wear_armor(self, raw):
        for i, st in enumerate(self.armor):
            if st:
                lvl = ench_level(st, "unbreaking")
                if lvl and random.random() < lvl / (lvl + 1.0):
                    continue
                st[2] -= max(1, int(raw / 4))
                if st[2] <= 0:
                    self.armor[i] = None
                    self.say(f"Сломалось: {NAMES[st[0]]}", 120)

    def equip_slot(self, idx):
        st = self.slots[idx]
        if not st or st[0] not in ARMOR:
            return
        pi = ARMOR[st[0]][0]
        self.slots[idx] = self.armor[pi]
        self.armor[pi] = st
        self.say(f"Надето: {NAMES[st[0]]}", 80)

    def eat_slot(self, idx):
        st = self.slots[idx]
        if not st or st[0] not in FOOD:
            return
        if self.food >= 20:
            self.say("Ты не голоден", 60)
            return
        self.food = min(20.0, self.food + FOOD[st[0]])
        st[1] -= 1
        if st[1] <= 0:
            self.slots[idx] = None
        self.say(f"Съедено: {NAMES[st[0]]}", 80)

    def eat(self):
        if self.mode == "creative":
            return
        if self.food >= 20:
            self.say("Ты не голоден", 60)
            return
        st = self.slots[self.selected]
        idx = self.selected if st and st[0] in FOOD else None
        if idx is None:
            for i, t in enumerate(self.slots):
                if t and t[0] in FOOD and (idx is None or FOOD[t[0]] > FOOD[self.slots[idx][0]]):
                    idx = i
        if idx is None:
            self.say("Нет еды (свинину можно пожарить в печи)", 90)
            return
        self.eat_slot(idx)

    def update_hunger(self):
        if self.mode == "creative":
            self.food = 20.0
            return
        if self.mode == "peaceful":
            self.food = 20.0
            self.regen += 1
            if self.regen >= 60:
                self.regen = 0
                if self.hp < MAXHP:
                    self.hp += 1
            return
        moving = abs(self.vx) > 0.01
        self.exh += 0.0004 + (0.0004 if moving else 0.0)
        if self.exh >= 1:
            self.exh -= 1
            self.food = max(0.0, self.food - 1)
        self.regen += 1
        if self.food >= 18 and self.hp < MAXHP:
            if self.regen >= 150:
                self.regen = 0
                self.hp += 1
        elif self.food <= 0:
            if self.regen >= 240:
                self.regen = 0
                if self.mode == "hardcore" or self.hp > 1:
                    self.hp -= 1
                    self.say("Ты голодаешь! Найди еду", 90)
                    if self.hp <= 0:
                        self.cause = "Ты умер от голода"
                        self.die()
        else:
            self.regen = 0

    # =====================================================================
    # печи
    # =====================================================================
    def update_furnaces(self):
        for key in list(self.furnaces):
            f = self.furnaces[key]
            if self.get(key[0], key[1]) != FURNACE:
                del self.furnaces[key]
                continue
            sl = f["slots"]
            fin, fuel, fout = sl
            out_item = SMELT.get(fin[0]) if fin else None
            can = out_item is not None and (
                fout is None or (fout[0] == out_item and fout[1] < 64))
            if f["burn"] > 0:
                f["burn"] -= 1
            if can:
                if f["burn"] <= 0 and fuel:
                    f["burn"] = f["burn_max"] = FUEL_VALUE[fuel[0]] * COOK_TIME
                    fuel[1] -= 1
                    if fuel[1] <= 0:
                        sl[1] = None
                if f["burn"] > 0:
                    f["cook"] += 1
                    if f["cook"] >= COOK_TIME:
                        f["cook"] = 0
                        fin[1] -= 1
                        if fin[1] <= 0:
                            sl[0] = None
                        if fout is None:
                            sl[2] = make_stack(out_item, 1)
                        else:
                            fout[1] += 1
                else:
                    f["cook"] = max(0, f["cook"] - 2)
            else:
                f["cook"] = max(0, f["cook"] - 2)

    def drop_furnace(self, key, creative):
        f = self.furnaces.pop(key, None)
        if f and not creative:
            for st in f["slots"]:
                if st:
                    self.add_stack(st)

    # =====================================================================
    # торговля
    # =====================================================================
    def do_trade(self, trade):
        give, (item, n) = trade
        v = self.ui_data
        if self.ui != "trade" or v is None or v.hp <= 0:
            return
        if math.hypot(v.x + v.w / 2 - (self.px + PW / 2),
                      v.y + v.h / 2 - (self.py + PH / 2)) > 6:
            self.say("Слишком далеко от жителя")
            return
        if not all(self.have(i) >= c for i, c in give.items()):
            self.say("Не хватает предметов для обмена")
            return
        for i, c in give.items():
            self.take(i, c)
        if not self.can_add(item, n):
            for i, c in give.items():
                self.add(i, c)
            self.say("Инвентарь полон!")
            return
        self.add(item, n)
        self.say(f"Обмен: получено {NAMES[item]} ×{n}")

    # =====================================================================
    # окна: инвентарь, верстак, печь, творческий режим, торговля, рецепты
    # =====================================================================
    def open_ui(self, kind, data=None):
        self.close_ui()
        self.ui = kind
        self.ui_data = data
        self.scroll_off = 0
        self.charge = 0
        if kind == "inv":
            self.grid_w = 2
        elif kind == "table":
            self.grid_w = 3
        self.grid = [None] * (self.grid_w ** 2) if kind in ("inv", "table") else []
        self.ench_slot = [None]
        if kind == "furnace":
            self.furnaces.setdefault(data, new_furnace())
        self.buttons.clear()
        self.keys.clear()
        self.mining = None

    def close_ui(self):
        if self.ui is None:
            return
        for st in list(self.grid) + [self.cursor] + list(self.ench_slot):
            if st:
                self.add_stack(st)
        self.grid = []
        self.cursor = None
        self.ench_slot = [None]
        self.ui = None
        self.ui_data = None

    def open_book(self):
        self.book_prev = self.ui
        self.ui = "book"
        self.scroll_off = 0

    def book_back(self):
        self.ui = self.book_prev
        self.scroll_off = 0

    def craft_result(self):
        if not self.grid:
            return None
        w = self.grid_w
        return match_recipe([st[0] if st else None for st in self.grid], w, w)

    def cont_info(self, cont, idx):
        """(массив ячеек, функция допуска предмета) для контейнера."""
        if cont == "inv":
            return self.slots, lambda it: True
        if cont == "grid":
            return self.grid, lambda it: True
        if cont == "ench":
            return self.ench_slot, lambda it: ench_cat(it) is not None
        if cont == "armor":
            return self.armor, lambda it: it in ARMOR and ARMOR[it][0] == idx
        if cont == "furn":
            f = self.furnaces.get(self.ui_data)
            if f is None:
                return None, None
            if idx == 0:
                return f["slots"], lambda it: it in SMELT
            if idx == 1:
                return f["slots"], lambda it: it in FUEL_VALUE
            return f["slots"], lambda it: False
        return None, None

    def slot_stack(self, cont, idx):
        if cont == "out":
            res = self.craft_result()
            return make_stack(*res) if res else None
        if cont == "pal":
            return make_stack(self.pal_items[idx], 1)
        arr, _ = self.cont_info(cont, idx)
        return arr[idx] if arr is not None else None

    def ui_click(self, x, y, button, shift=False):
        for x0, y0, x1, y1, cont, idx in self.ui_slots:
            if x0 <= x <= x1 and y0 <= y <= y1:
                if shift and cont in ("inv", "armor", "grid", "furn"):
                    self.slot_shift(cont, idx)
                else:
                    self.slot_click(cont, idx, button)
                return

    def slot_shift(self, cont, idx):
        arr, ok = self.cont_info(cont, idx)
        if arr is None or arr[idx] is None:
            return
        st = arr[idx]
        if cont == "inv":
            if st[0] in ARMOR:
                pi = ARMOR[st[0]][0]
                arr[idx], self.armor[pi] = self.armor[pi], st
            return
        if self.can_add(st[0], st[1]):
            self.add_stack(st)
            arr[idx] = None
        else:
            self.say("Инвентарь полон!", 60)

    def slot_click(self, cont, idx, button):
        c = self.cursor
        if cont == "out":
            res = self.craft_result()
            if res is None:
                return
            item, n = res
            if c is None:
                self.cursor = make_stack(item, n)
            elif c[0] == item and stack_limit(item) > 1 and c[1] + n <= 64:
                c[1] += n
            else:
                return
            for i, st in enumerate(self.grid):
                if st:
                    st[1] -= 1
                    if st[1] <= 0:
                        self.grid[i] = None
            return
        if cont == "pal":
            if c is not None:
                self.cursor = None
                return
            item = self.pal_items[idx]
            self.cursor = make_stack(item, stack_limit(item) if button == 1 else 1)
            return
        if cont == "trash":
            self.cursor = None
            return
        arr, ok = self.cont_info(cont, idx)
        if arr is None:
            return
        st = arr[idx]
        if cont == "furn" and idx == 2:          # выход печи: только забрать
            if st is None:
                return
            if c is None:
                self.cursor = st
                arr[idx] = None
            elif c[0] == st[0] and c[1] + st[1] <= 64:
                c[1] += st[1]
                arr[idx] = None
            return
        if button == 1:
            if c is None:
                if st:
                    self.cursor = st
                    arr[idx] = None
            else:
                if not ok(c[0]):
                    return
                if st is None:
                    arr[idx] = c
                    self.cursor = None
                elif st[0] == c[0] and stack_limit(c[0]) > 1:
                    tot = st[1] + c[1]
                    if tot <= 64:
                        st[1] = tot
                        self.cursor = None
                    else:
                        st[1] = 64
                        c[1] = tot - 64
                else:
                    arr[idx], self.cursor = c, st
        else:
            if c is None:
                if st:
                    half = (st[1] + 1) // 2
                    if half >= st[1]:
                        self.cursor = st
                        arr[idx] = None
                    else:
                        self.cursor = list(st)
                        self.cursor[1] = half
                        st[1] -= half
            else:
                if not ok(c[0]):
                    return
                if st is None:
                    arr[idx] = list(c)
                    arr[idx][1] = 1
                    c[1] -= 1
                elif st[0] == c[0] and stack_limit(c[0]) > 1 and st[1] < 64:
                    st[1] += 1
                    c[1] -= 1
                else:
                    return
                if c[1] <= 0:
                    self.cursor = None

    # ---------- отрисовка предметов ----------
    # =====================================================================
    # измерения и порталы
    # =====================================================================
    def pack_dim(self):
        return dict(world=self.world, top=self.top, biome=self.biome,
                    village_spans=self.village_spans, ents=self.ents,
                    furnaces=self.furnaces, arrows=self.arrows, W=self.W)

    def unpack_dim(self, st):
        self.world = st["world"]
        self.top = st["top"]
        self.biome = st["biome"]
        self.village_spans = st["village_spans"]
        self.ents = st["ents"]
        self.furnaces = st["furnaces"]
        self.arrows = st["arrows"]
        self.W = st["W"]

    def switch_dim(self, new):
        if new == self.dim:
            return
        self.dims[self.dim] = self.pack_dim()
        st = self.dims.pop(new, None)
        if st is None:
            st = self.gen_nether()
        self.unpack_dim(st)
        self.dim = new
        self.mining = None
        self.charge = 0

    def surface_y(self, x):
        for y in range(0, WORLD_H):
            b = self.world[y][x]
            if b != AIR and b not in PASSABLE:
                return y
        return WORLD_H - 4

    def nether_ground(self, tx):
        for d in sorted(range(-48, 49), key=abs):
            x = tx + d
            if not (6 <= x < self.W - 8):
                continue
            y = WORLD_H - 4
            while y > 3 and self.world[y][x] not in (AIR, LAVA):
                y -= 1
            if self.world[y][x] == AIR and y > 4:
                return x, y + 1
        return None

    def find_portal_near(self, tx, r):
        best = None
        for x in range(max(0, tx - r), min(self.W, tx + r + 1)):
            for y in range(1, WORLD_H - 1):
                if self.world[y][x] == PORTAL and self.world[y + 1][x] != PORTAL:
                    d = abs(x - tx)
                    if best is None or d < best[0]:
                        best = (d, x, y)
                    break
        return (best[1], best[2]) if best else None

    def build_portal(self, x0, base_y, fill):
        w = self.world
        for yy in range(base_y - 7, base_y + 1):
            for xx in range(x0 - 2, x0 + 6):
                if 0 <= xx < self.W and 3 <= yy < WORLD_H - 3:
                    w[yy][xx] = AIR
        for xx in range(x0 - 2, x0 + 6):
            if 0 <= xx < self.W and w[base_y + 1][xx] in (AIR, LAVA) + PASSABLE:
                w[base_y + 1][xx] = fill
        for xx in range(x0, x0 + 4):
            w[base_y][xx] = OBSIDIAN
            w[base_y - 4][xx] = OBSIDIAN
        for yy in range(base_y - 3, base_y):
            w[yy][x0] = OBSIDIAN
            w[yy][x0 + 3] = OBSIDIAN
            w[yy][x0 + 1] = PORTAL
            w[yy][x0 + 2] = PORTAL

    def build_exit_portal(self, tx):
        if self.dim == "nether":
            g = self.nether_ground(tx)
            if g is None:
                x, gy = tx, 80
            else:
                x, gy = g
            fill = NETHERRACK
        else:
            x = tx
            gy = self.surface_y(x)
            fill = STONE
        x0 = max(3, min(self.W - 9, x - 1))
        base_y = gy - 1
        self.build_portal(x0, base_y, fill)
        return x0 + 1, base_y - 1

    def travel(self):
        target = "nether" if self.dim == "over" else "over"
        ox = int(self.px + PW / 2)
        tx = ox // PORTAL_RATIO if target == "nether" else ox * PORTAL_RATIO
        self.close_ui()
        self.switch_dim(target)
        tx = max(4, min(self.W - 9, tx))
        pos = self.find_portal_near(tx, 40 if target == "nether" else 160)
        if pos is None:
            pos = self.build_exit_portal(tx)
        x, y = pos
        self.px = x + 0.5 - PW / 2
        self.py = y + 1 - PH - 0.01
        self.vx = self.vy = 0.0
        self.kbx = 0.0
        self.fall_top = None
        self.portal_t = 0
        self.portal_lock = True
        self.arrows = []
        self.say("Ты в Незере! Осторожно: лава и гасты." if target == "nether"
                 else "Ты вернулся в обычный мир.", 200)

    def find_portal_region(self, tx, ty):
        if self.get(tx, ty) != AIR:
            return None
        seen = {(tx, ty)}
        stack = [(tx, ty)]
        while stack:
            x, y = stack.pop()
            for nx, ny in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                if (nx, ny) not in seen and self.get(nx, ny) == AIR:
                    seen.add((nx, ny))
                    if len(seen) > 60:
                        return None
                    stack.append((nx, ny))
        xs = [p[0] for p in seen]
        ys = [p[1] for p in seen]
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        w, h = x1 - x0 + 1, y1 - y0 + 1
        if len(seen) != w * h or not (2 <= w <= 6 and 3 <= h <= 8):
            return None
        for x in range(x0, x1 + 1):
            if self.get(x, y0 - 1) != OBSIDIAN or self.get(x, y1 + 1) != OBSIDIAN:
                return None
        for y in range(y0, y1 + 1):
            if self.get(x0 - 1, y) != OBSIDIAN or self.get(x1 + 1, y) != OBSIDIAN:
                return None
        return x0, y0, x1, y1

    def try_light(self):
        tx, ty = self.mouse_tile()
        if not self.in_reach(tx, ty):
            return
        reg = None
        for x, y in ((tx, ty), (tx + 1, ty), (tx - 1, ty), (tx, ty + 1), (tx, ty - 1)):
            if self.get(x, y) == AIR:
                reg = self.find_portal_region(x, y)
                if reg:
                    break
        if reg is None:
            self.say("Нужна рамка из обсидиана (внутри не меньше 2x3). Кликни внутрь рамки.", 160)
            return
        x0, y0, x1, y1 = reg
        for yy in range(y0, y1 + 1):
            for xx in range(x0, x1 + 1):
                self.world[yy][xx] = PORTAL
        self.wear_tool(self.selected)
        self.say("Портал открыт! Зайди внутрь и подожди пару секунд.", 160)

    def draw_item(self, x, y, s, item):
        c = self.canvas
        col = COLORS.get(item, "#ff00ff")

        def P(fx, fy):
            return (x + fx * s, y + fy * s)

        lw = max(2, int(s // 8))
        if item in BLOCKS:
            c.create_rectangle(x, y, x + s, y + s, fill=col, outline="#222222")
            if item in ORE_DOTS:
                for fx, fy in ((.12, .12), (.55, .18), (.22, .55), (.6, .6)):
                    c.create_rectangle(*P(fx, fy), *P(fx + .24, fy + .24),
                                       fill=ORE_DOTS[item], outline="")
            elif item == TABLE:
                c.create_rectangle(*P(0, 0), *P(1, .3), fill="#d19a58", outline="#222222")
            elif item == FURNACE:
                c.create_rectangle(*P(.22, .4), *P(.78, .85), fill="#111111", outline="")
            return
        if item in TOOLS:
            kind, mi = TOOLS[item]
            mc = MATS[mi][7]
            if kind == "sword":
                c.create_line(*P(.5, .06), *P(.5, .68), fill=mc, width=lw + 2)
                c.create_line(*P(.25, .7), *P(.75, .7), fill="#5a3b1a", width=lw)
                c.create_line(*P(.5, .7), *P(.5, .95), fill="#7b5a35", width=lw)
                return
            c.create_line(*P(.5, .25), *P(.5, .95), fill="#7b5a35", width=lw)
            if kind == "pickaxe":
                c.create_line(*P(.1, .42), *P(.5, .12), *P(.9, .42), fill=mc, width=lw + 2)
            elif kind == "axe":
                c.create_polygon(*P(.5, .1), *P(.9, .2), *P(.9, .55), *P(.5, .42),
                                 fill=mc, outline="#333333")
            else:
                c.create_oval(*P(.3, .05), *P(.7, .42), fill=mc, outline="#333333")
            return
        if item in ARMOR:
            pi = ARMOR[item][0]
            o = "#333333"
            if pi == 0:
                c.create_rectangle(*P(.15, .2), *P(.85, .5), fill=col, outline=o)
                c.create_rectangle(*P(.15, .5), *P(.35, .78), fill=col, outline=o)
                c.create_rectangle(*P(.65, .5), *P(.85, .78), fill=col, outline=o)
            elif pi == 1:
                c.create_rectangle(*P(.28, .12), *P(.72, .9), fill=col, outline=o)
                c.create_rectangle(*P(.06, .12), *P(.28, .5), fill=col, outline=o)
                c.create_rectangle(*P(.72, .12), *P(.94, .5), fill=col, outline=o)
            elif pi == 2:
                c.create_rectangle(*P(.2, .1), *P(.8, .4), fill=col, outline=o)
                c.create_rectangle(*P(.2, .4), *P(.48, .92), fill=col, outline=o)
                c.create_rectangle(*P(.52, .4), *P(.8, .92), fill=col, outline=o)
            else:
                c.create_rectangle(*P(.08, .42), *P(.42, .88), fill=col, outline=o)
                c.create_rectangle(*P(.58, .42), *P(.92, .88), fill=col, outline=o)
                c.create_rectangle(*P(.08, .76), *P(.42, .88), fill="#333333", outline="")
                c.create_rectangle(*P(.58, .76), *P(.92, .88), fill="#333333", outline="")
            return
        if item == BOW:
            c.create_line(*P(.3, .08), *P(.8, .3), *P(.8, .7), *P(.3, .92), smooth=True,
                          fill="#8b5a2b", width=lw + 1)
            c.create_line(*P(.3, .08), *P(.3, .92), fill="#eeeeee", width=1)
        elif item == ARROW:
            c.create_line(*P(.15, .85), *P(.8, .2), fill="#bbbbbb", width=lw)
            c.create_polygon(*P(.9, .1), *P(.66, .16), *P(.84, .34), fill="#dddddd", outline="#555555")
            c.create_line(*P(.15, .85), *P(.08, .7), fill="#e07070", width=lw)
            c.create_line(*P(.15, .85), *P(.3, .92), fill="#e07070", width=lw)
        elif item == STRING:
            c.create_line(*P(.15, .8), *P(.35, .3), *P(.5, .75), *P(.65, .25), *P(.85, .7),
                          fill="#eeeeee", width=lw)
        elif item == LIGHTER:
            c.create_rectangle(*P(.22, .45), *P(.78, .88), fill="#9a9a9a", outline="#333333")
            c.create_oval(*P(.38, .1), *P(.62, .48), fill="#ff9a1a", outline="#aa4400")
        elif item == PAPER:
            c.create_rectangle(*P(.2, .12), *P(.8, .88), fill="#f5f5dc", outline="#999977")
            c.create_line(*P(.3, .35), *P(.7, .35), fill="#aaa", width=1)
            c.create_line(*P(.3, .55), *P(.7, .55), fill="#aaa", width=1)
        elif item == BOOK:
            c.create_rectangle(*P(.18, .12), *P(.82, .88), fill="#8b4513", outline="#3a1a05")
            c.create_rectangle(*P(.3, .22), *P(.74, .78), fill="#f0e0b0", outline="")
        elif item == QUARTZ:
            c.create_polygon(*P(.5, .1), *P(.85, .5), *P(.5, .9), *P(.15, .5),
                             fill=col, outline="#aaa090")
        elif item == COAL:
            c.create_oval(*P(.18, .22), *P(.82, .82), fill=col, outline="#000000")
        elif item in (IRON_RAW, GOLD_RAW):
            c.create_oval(*P(.15, .2), *P(.85, .85), fill=col, outline="#444444")
            c.create_oval(*P(.32, .32), *P(.5, .5), fill="#ffffff", outline="")
        elif item in (IRON_INGOT, GOLD_INGOT):
            c.create_polygon(*P(.12, .6), *P(.3, .3), *P(.9, .3), *P(.72, .6),
                             fill=col, outline="#444444")
            c.create_polygon(*P(.12, .6), *P(.72, .6), *P(.72, .78), *P(.12, .78),
                             fill=shade(col, 2), outline="#444444")
        elif item == DIAMOND:
            c.create_polygon(*P(.5, .08), *P(.88, .38), *P(.5, .92), *P(.12, .38),
                             fill=col, outline="#1a7a7a")
        elif item == EMERALD:
            c.create_polygon(*P(.3, .12), *P(.7, .12), *P(.92, .5), *P(.7, .88),
                             *P(.3, .88), *P(.08, .5), fill=col, outline="#1a6a3a")
        elif item == STICK:
            c.create_line(*P(.2, .88), *P(.8, .12), fill=col, width=lw)
        elif item == BONE:
            c.create_line(*P(.2, .8), *P(.8, .2), fill=col, width=lw + 1)
            c.create_oval(*P(.08, .68), *P(.3, .92), fill=col, outline="")
            c.create_oval(*P(.7, .08), *P(.92, .32), fill=col, outline="")
        elif item == GUNPOWDER:
            c.create_rectangle(*P(.2, .35), *P(.8, .8), fill=col, outline="#222233")
            c.create_rectangle(*P(.3, .45), *P(.4, .55), fill="#999999", outline="")
        elif item == ROTTEN:
            c.create_oval(*P(.12, .25), *P(.88, .8), fill=col, outline="#3a4a1a")
        elif item in (RAW_PORK, COOKED_PORK):
            c.create_oval(*P(.1, .25), *P(.9, .85), fill=col, outline="#442200")
            c.create_oval(*P(.25, .35), *P(.5, .5), fill=shade(col, 0) if False else "#ffe0e0"
                          if item == RAW_PORK else "#e0a060", outline="")
        elif item == APPLE:
            c.create_oval(*P(.15, .25), *P(.85, .92), fill=col, outline="#7a1010")
            c.create_line(*P(.5, .25), *P(.55, .08), fill="#5a3b1a", width=lw)
        else:
            c.create_rectangle(*P(.15, .15), *P(.85, .85), fill=col, outline="#222222")

    def draw_dur(self, x, y, w, st):
        if st[2] is None:
            return
        mx = max_dur(st[0])
        if mx is None or st[2] >= mx:
            return
        r = max(0.0, st[2] / mx)
        col = "#4caf50" if r > 0.5 else ("#ffc107" if r > 0.25 else "#f44336")
        self.canvas.create_rectangle(x, y, x + w, y + 3, fill="#000000", outline="")
        self.canvas.create_rectangle(x, y, x + w * r, y + 3, fill=col, outline="")

    def draw_slot(self, x, y, cont, idx, st, size=40):
        c = self.canvas
        mx, my = self.mouse
        hover = x <= mx <= x + size and y <= my <= y + size
        c.create_rectangle(x, y, x + size, y + size,
                           fill="#b4cdf5" if hover else "#8b8b8b",
                           outline="#373737", width=2)
        if st:
            self.draw_item(x + 5, y + 5, size - 10, st[0])
            if len(st) > 3 and st[3]:
                self.draw_glint(x + 5, y + 5, size - 10)
            if st[1] > 1:
                c.create_text(x + size - 3, y + size - 3, anchor="se", text=str(st[1]),
                              fill="black", font=("Arial", 10, "bold"))
                c.create_text(x + size - 4, y + size - 4, anchor="se", text=str(st[1]),
                              fill="white", font=("Arial", 10, "bold"))
            self.draw_dur(x + 5, y + size - 8, size - 10, st)
        self.ui_slots.append((x, y, x + size, y + size, cont, idx))

    def draw_arrow(self, x, y, ratio=None):
        c = self.canvas
        pts = (x, y + 6, x + 20, y + 6, x + 20, y, x + 34, y + 12, x + 20, y + 24, x + 20, y + 18, x, y + 18)
        c.create_polygon(*pts, fill="#6a6a6a", outline="#333333")
        if ratio:
            c.create_rectangle(x + 1, y + 7, x + 1 + 30 * ratio, y + 17, fill="#3aa03a", outline="")

    def draw_panel(self, title):
        c = self.canvas
        c.create_rectangle(UI_X, UI_Y, UI_X + UI_W, UI_Y + UI_H, fill="#c6c6c6",
                           outline="#222222", width=3)
        c.create_text(UI_X + 14, UI_Y + 8, anchor="nw", text=title, fill="#404040",
                      font=("Arial", 12, "bold"))

    def draw_preview(self, x, y, w, h):
        c = self.canvas
        c.create_rectangle(x, y, x + w, y + h, fill="#8b8b8b", outline="#373737", width=2)
        cx = x + w / 2
        ac = [(COLORS[st[0]] if st else None) for st in self.armor]
        c.create_rectangle(cx - 18, y + 46, cx + 18, y + 108, fill=ac[1] or "#3b6fd4", outline="black")
        c.create_rectangle(cx - 18, y + 108, cx - 1, y + 150, fill=ac[2] or "#2c4a8c", outline="black")
        c.create_rectangle(cx + 1, y + 108, cx + 18, y + 150, fill=ac[2] or "#2c4a8c", outline="black")
        if ac[3]:
            c.create_rectangle(cx - 18, y + 140, cx - 1, y + 150, fill=ac[3], outline="black")
            c.create_rectangle(cx + 1, y + 140, cx + 18, y + 150, fill=ac[3], outline="black")
        c.create_rectangle(cx - 15, y + 18, cx + 15, y + 46, fill="#f1c27d", outline="black")
        if ac[0]:
            c.create_rectangle(cx - 16, y + 16, cx + 16, y + 28, fill=ac[0], outline="black")
        c.create_text(cx, y + h - 8, text=f"Защита: {self.armor_points()}", fill="#202020",
                      font=("Arial", 9, "bold"))

    def draw_tooltip(self, x, y, st):
        c = self.canvas
        item = st[0]
        lines = [(NAMES.get(item, "?"), "#ffffff")]
        if len(st) > 3 and st[3]:
            for k, lv in st[3].items():
                lines.append((ench_text(k, lv), "#c27bff"))
        if item in ARMOR:
            pi, mi = ARMOR[item]
            lines.append((f"Защита: {ARMOR_MATS[mi][4][pi]}", "#bbbbbb"))
        if st[2] is not None:
            lines.append((f"Прочность: {st[2]}/{max_dur(item)}", "#bbbbbb"))
        if item in FOOD:
            lines.append((f"Сытость: +{FOOD[item]}", "#bbbbbb"))
        if item == BOW:
            lines.append(("Зажми ЛКМ - натяни, отпусти - выстрел", "#888888"))
        w = max(len(t) for t, _ in lines) * 7 + 14
        h = len(lines) * 16 + 8
        x = min(x, CW - w - 4)
        y = min(y, CH - h - 4)
        c.create_rectangle(x, y, x + w, y + h, fill="#1a0a2a", outline="#6a3da0", width=2)
        for i, (t, colr) in enumerate(lines):
            c.create_text(x + 7, y + 5 + i * 16, anchor="nw", text=t, fill=colr,
                          font=("Arial", 10, "bold" if i == 0 else "normal"))

    def draw_cursor_tooltip(self):
        c = self.canvas
        mx, my = self.mouse
        if self.cursor is None:
            for x0, y0, x1, y1, cont, idx in self.ui_slots:
                if x0 <= mx <= x1 and y0 <= my <= y1:
                    st = self.slot_stack(cont, idx)
                    if st:
                        self.draw_tooltip(mx + 14, my + 14, st)
                    break
        else:
            self.draw_item(mx - 16, my - 16, 32, self.cursor[0])
            if len(self.cursor) > 3 and self.cursor[3]:
                self.draw_glint(mx - 16, my - 16, 32)
            if self.cursor[1] > 1:
                c.create_text(mx + 17, my + 17, anchor="se", text=str(self.cursor[1]),
                              fill="white", font=("Arial", 10, "bold"))

    def draw_ui(self):
        k = self.ui
        if k == "furnace" and self.furnaces.get(self.ui_data) is None:
            self.close_ui()
            return
        if k == "book":
            self.draw_book()
            return
        if k == "trade":
            self.draw_trade_ui()
            return
        c = self.canvas
        titles = {"inv": "Инвентарь", "table": "Верстак", "furnace": "Печь",
                  "enchant": "Зачарование",
                  "creative": "Творческий режим - выбери предмет"}
        self.draw_panel(titles[k])
        ix = UI_X + 14
        if k == "inv":
            for i in range(4):
                self.draw_slot(ix, UI_Y + 30 + i * SL, "armor", i, self.armor[i])
            self.draw_preview(UI_X + 64, UI_Y + 30, 120, 168)
            for r in range(2):
                for col in range(2):
                    n = r * 2 + col
                    self.draw_slot(UI_X + 250 + col * SL, UI_Y + 70 + r * SL, "grid", n, self.grid[n])
            self.draw_arrow(UI_X + 340, UI_Y + 98)
            res = self.craft_result()
            self.draw_slot(UI_X + 382, UI_Y + 92, "out", 0, make_stack(*res) if res else None)
        elif k == "table":
            for r in range(3):
                for col in range(3):
                    n = r * 3 + col
                    self.draw_slot(UI_X + 80 + col * SL, UI_Y + 40 + r * SL, "grid", n, self.grid[n])
            self.draw_arrow(UI_X + 222, UI_Y + 90)
            res = self.craft_result()
            self.draw_slot(UI_X + 272, UI_Y + 82, "out", 0, make_stack(*res) if res else None)
        elif k == "furnace":
            f = self.furnaces[self.ui_data]
            sl = f["slots"]
            self.draw_slot(UI_X + 150, UI_Y + 40, "furn", 0, sl[0])
            fx, fy = UI_X + 160, UI_Y + 86
            c.create_rectangle(fx, fy, fx + 20, fy + 36, fill="#555555", outline="#222222")
            if f["burn"] > 0:
                r = f["burn"] / max(1, f["burn_max"])
                c.create_rectangle(fx + 2, fy + 34 - 32 * r, fx + 18, fy + 34, fill="#ff8a1f", outline="")
            self.draw_slot(UI_X + 150, UI_Y + 128, "furn", 1, sl[1])
            self.draw_arrow(UI_X + 212, UI_Y + 96, f["cook"] / COOK_TIME if f["cook"] else None)
            self.draw_slot(UI_X + 266, UI_Y + 90, "furn", 2, sl[2])
            c.create_text(UI_X + 14, UI_Y + 178, anchor="nw", fill="#404040", font=("Arial", 9),
                          text="Вверху - что плавить, внизу - топливо (уголь, дерево, доски, палки)")
        elif k == "enchant":
            self.draw_enchant_top()
        else:   # creative
            vis = 4
            rows = (len(self.pal_items) + 8) // 9
            self.scroll_off = max(0, min(self.scroll_off, max(0, rows - vis)))
            for r in range(vis):
                for col in range(9):
                    n = (self.scroll_off + r) * 9 + col
                    if n < len(self.pal_items):
                        self.draw_slot(ix + col * SL, UI_Y + 30 + r * SL, "pal", n,
                                       make_stack(self.pal_items[n], 1))
            c.create_text(UI_X + UI_W - 14, UI_Y + 8, anchor="ne", fill="#404040", font=("Arial", 9),
                          text="колёсико - прокрутка, клик по ячейке - убрать предмет в корзину")

        c.create_text(ix, UI_Y + 200, anchor="nw", text="Инвентарь", fill="#404040",
                      font=("Arial", 10, "bold"))
        for r in range(3):
            for col in range(9):
                n = 9 + r * 9 + col
                self.draw_slot(ix + col * SL, UI_Y + 218 + r * SL, "inv", n, self.slots[n])
        for col in range(9):
            self.draw_slot(ix + col * SL, UI_Y + 352, "inv", col, self.slots[col])
            if col == self.selected:
                c.create_rectangle(ix + col * SL - 1, UI_Y + 351, ix + col * SL + 41, UI_Y + 393,
                                   outline="#ffd700", width=3)
        if k == "creative":
            self.draw_slot(ix + 9 * SL + 6, UI_Y + 352, "trash", 0, None)
            c.create_text(ix + 9 * SL + 26, UI_Y + 372, text="Корзина", fill="#802020",
                          font=("Arial", 8, "bold"))
        if k in ("inv", "table"):
            self.button(UI_X + UI_W - 110, UI_Y + 4, 98, 24, "Рецепты", self.open_book)
        self.draw_cursor_tooltip()

    def apply_enchant(self, i):
        st = self.ench_slot[0]
        if not st or ench_cat(st[0]) is None or (len(st) > 3 and st[3]):
            return
        offers = gen_offers(st[0], self.ench_seed)
        if i >= len(offers):
            return
        cost, en = offers[i]
        if self.xp_level < cost:
            self.say("Не хватает уровней опыта!", 90)
            return
        self.xp_level -= cost
        st[3] = dict(en)
        self.ench_seed += 1
        self.say("Предмет зачарован!", 90)

    def draw_enchant_top(self):
        c = self.canvas
        st = self.ench_slot[0]
        c.create_text(UI_X + 14, UI_Y + 30, anchor="nw", fill="#404040", font=("Arial", 10, "bold"),
                      text=f"Твой уровень опыта: {self.xp_level}   (до следующего: "
                           f"{self.xp_prog}/{self.xp_need(self.xp_level)})")
        self.draw_slot(UI_X + 26, UI_Y + 90, "ench", 0, st)
        c.create_text(UI_X + 46, UI_Y + 136, text="Предмет", fill="#404040", font=("Arial", 9))
        offers = []
        msg = "Положи кирку, топор, лопату, меч, лук или броню"
        if st:
            if ench_cat(st[0]) is None:
                msg = "Этот предмет нельзя зачаровать"
            elif len(st) > 3 and st[3]:
                msg = "Предмет уже зачарован"
            else:
                offers = gen_offers(st[0], self.ench_seed)
                msg = ""
        if msg:
            c.create_text(UI_X + 96, UI_Y + 100, anchor="nw", fill="#404040", font=("Arial", 10), text=msg)
        x, w = UI_X + 90, UI_W - 104
        for i, (cost, en) in enumerate(offers):
            y = UI_Y + 56 + i * 46
            ok = self.xp_level >= cost
            c.create_rectangle(x, y, x + w, y + 40, fill="#8b8b8b" if ok else "#a9a9a9",
                               outline="#373737", width=2)
            txt = ", ".join(ench_text(k, lv) for k, lv in en.items())
            c.create_text(x + 8, y + 5, anchor="nw", text=txt, fill="#101010" if ok else "#707070",
                          font=("Arial", 11, "bold"))
            c.create_text(x + 8, y + 23, anchor="nw", fill="#303030" if ok else "#808080",
                          font=("Arial", 9),
                          text=f"Стоит {cost} ур. опыта" if ok else f"Нужно {cost} ур. опыта")
            c.create_oval(x + w - 34, y + 6, x + w - 6, y + 34, fill="#3a8a3a" if ok else "#555555",
                          outline="#222222")
            c.create_text(x + w - 20, y + 20, text=str(cost), fill="white", font=("Arial", 11, "bold"))
            self.hitboxes.append((x, y, x + w, y + 40, lambda i=i: self.apply_enchant(i)))

    def draw_glint(self, x, y, s):
        c = self.canvas
        c.create_line(x + 2, y + s * 0.55, x + s * 0.55, y + 2, fill="#c27bff", width=2)
        c.create_line(x + s * 0.3, y + s - 2, x + s - 2, y + s * 0.3, fill="#a64dff", width=2)
        c.create_oval(x + s - 7, y + 1, x + s - 2, y + 6, fill="#e0b0ff", outline="")

    def draw_trade_row(self, x, y, w, h, item, title, sub, enabled, fn):
        c = self.canvas
        c.create_rectangle(x, y, x + w, y + h, fill="#8b8b8b" if enabled else "#a9a9a9",
                           outline="#373737", width=2)
        self.draw_item(x + 6, y + 4, h - 8, item)
        c.create_text(x + h + 4, y + 3, anchor="nw", text=title,
                      fill="#101010" if enabled else "#707070", font=("Arial", 11, "bold"))
        c.create_text(x + h + 4, y + 21, anchor="nw", text=sub,
                      fill="#303030" if enabled else "#808080", font=("Arial", 9))
        self.hitboxes.append((x, y, x + w, y + h, fn))

    def draw_trade_ui(self):
        c = self.canvas
        v = self.ui_data
        if v is None or v.prof not in PROFS:
            self.close_ui()
            return
        self.draw_panel("Торговля: " + PROFS[v.prof][0])
        c.create_text(UI_X + 14, UI_Y + 32, anchor="nw", fill="#404040", font=("Arial", 10, "bold"),
                      text=f"Валюта - изумруды.  У тебя изумрудов: {self.have(EMERALD)}")
        trades = PROFS[v.prof][2]
        rw, rh, pitch = UI_W - 28, 40, 44
        top = UI_Y + 58
        vis = max(1, int((UI_H - 58 - 8) // pitch))
        self.scroll_off = max(0, min(self.scroll_off, max(0, len(trades) - vis)))
        for i, t in enumerate(trades[self.scroll_off:self.scroll_off + vis]):
            give, (item, n) = t
            sub = "Отдать: " + ", ".join(f"{NAMES[g]} ×{cnt} (есть {self.have(g)})"
                                         for g, cnt in give.items())
            ok = all(self.have(g) >= cnt for g, cnt in give.items())
            self.draw_trade_row(UI_X + 14, top + i * pitch, rw, rh, item,
                                f"Получить: {NAMES[item]} ×{n}", sub, ok,
                                lambda t=t: self.do_trade(t))
        if len(trades) > vis:
            c.create_text(UI_X + UI_W // 2, UI_Y + UI_H - 6, anchor="s", fill="#404040",
                          font=("Arial", 9), text="Прокрутка: колёсико / стрелки")

    def draw_book(self):
        c = self.canvas
        self.draw_panel("Книга рецептов")
        self.button(UI_X + UI_W - 110, UI_Y + 4, 98, 24, "Назад", self.book_back)
        pitch = 58
        top = UI_Y + 34
        vis = max(1, int((UI_H - 34 - 6) // pitch))
        n = len(GRID_RECIPES)
        self.scroll_off = max(0, min(self.scroll_off, max(0, n - vis)))
        for i, rec in enumerate(GRID_RECIPES[self.scroll_off:self.scroll_off + vis]):
            y = top + i * pitch
            c.create_rectangle(UI_X + 10, y, UI_X + UI_W - 10, y + pitch - 4, fill="#b0b0b0",
                               outline="#555555")
            pat = rec["pat"]
            for r, row in enumerate(pat):
                for col, it in enumerate(row):
                    cx, cy = UI_X + 20 + col * 17, y + 2 + r * 17
                    c.create_rectangle(cx, cy, cx + 16, cy + 16, fill="#8b8b8b", outline="#444444")
                    if it is not None:
                        self.draw_item(cx + 1, cy + 1, 14, it)
            self.draw_arrow(UI_X + 82, y + 14)
            c.create_rectangle(UI_X + 126, y + 8, UI_X + 160, y + 42, fill="#8b8b8b", outline="#444444")
            self.draw_item(UI_X + 131, y + 13, 24, rec["out"])
            c.create_text(UI_X + 168, y + 10, anchor="nw", fill="#101010", font=("Arial", 11, "bold"),
                          text=f"{NAMES[rec['out']]} ×{rec['n']}")
            big = len(pat) > 2 or len(pat[0]) > 2
            c.create_text(UI_X + 168, y + 30, anchor="nw", fill="#303030", font=("Arial", 9),
                          text="нужен верстак (3x3)" if big else "можно в инвентаре (2x2)")
        c.create_text(UI_X + UI_W // 2, UI_Y + UI_H - 4, anchor="s", fill="#404040", font=("Arial", 9),
                      text="Прокрутка: колёсико / стрелки. Рисунок можно зеркально переворачивать.")

    def say(self, text, frames=150):
        self.msg = text
        self.msg_t = frames

    def near(self, block, r=NEAR_R):
        cx = self.px + PW / 2
        cy = self.py + PH / 2
        for ty in range(int(cy - r) - 1, int(cy + r) + 2):
            for tx in range(int(cx - r) - 1, int(cx + r) + 2):
                if (0 <= tx < self.W and 0 <= ty < WORLD_H
                        and self.world[ty][tx] == block
                        and math.hypot(tx + 0.5 - cx, ty + 0.5 - cy) <= r):
                    return True
        return False

    # =====================================================================
    # крафт, плавка, торговля
    # =====================================================================
    # =====================================================================
    # меню
    # =====================================================================
    # =====================================================================
    # ввод
    # =====================================================================
    def on_key_press(self, e):
        k = e.keysym.lower()
        if self.scene == "create":
            self.create_key(e, k)
            return
        if self.scene != "play":
            if k == "escape":
                self.back_scene()
            return
        if self.dead:
            return
        if self.paused:
            if k == "escape":
                self.paused = False
            return
        if self.ui in ("creative", "trade", "book") and k in ("up", "down"):
            self.wheel(-1 if k == "up" else 1)
            return
        if k in KEYMAP:
            self.keys.add(KEYMAP[k])
        elif k.isdigit():
            idx = int(k) - 1
            if 0 <= idx < HB:
                self.selected = idx
        elif k in ("e", "cyrillic_ie"):
            if self.ui is not None:
                self.close_ui()
            else:
                self.open_ui("creative" if self.mode == "creative" else "inv")
        elif k == "escape":
            if self.ui == "book":
                self.book_back()
            elif self.ui is not None:
                self.close_ui()
            else:
                self.open_pause()
        elif k in ("f", "cyrillic_a"):
            self.eat()

    def on_key_release(self, e):
        k = e.keysym.lower()
        if k in KEYMAP:
            self.keys.discard(KEYMAP[k])

    def on_motion(self, e):
        self.mouse = (e.x, e.y)

    def mouse_world(self):
        cx, cy = self.camera()
        return self.mouse[0] / TILE + cx, self.mouse[1] / TILE + cy

    def mouse_tile(self):
        mx, my = self.mouse_world()
        return math.floor(mx), math.floor(my)

    def ent_at_mouse(self, only=None):
        mx, my = self.mouse_world()
        pcx, pcy = self.px + PW / 2, self.py + PH / 2
        for e in self.ents:
            if e.hp <= 0:
                continue
            if only == "villager" and e.kind != "villager":
                continue
            if only == "mob" and e.kind == "villager":
                continue
            if (e.x - 0.15 <= mx <= e.x + e.w + 0.15
                    and e.y - 0.15 <= my <= e.y + e.h + 0.15):
                d = math.hypot(e.x + e.w / 2 - pcx, e.y + e.h / 2 - pcy)
                if d <= (REACH if e.kind == "villager" else ATTACK_R):
                    return e
        return None

    def on_button(self, e, b, down):
        self.mouse = (e.x, e.y)
        if not down:
            self.buttons.discard(b)
            if (b == 1 and self.scene == "play" and not self.paused and not self.dead
                    and self.charge > 0):
                self.fire_bow()
            return
        if self.scene != "play" or self.paused or self.dead:
            if b != 1:
                return
            for x0, y0, x1, y1, fn in list(self.hitboxes):
                if x0 <= e.x <= x1 and y0 <= e.y <= y1:
                    fn()
                    break
            return
        if self.ui is not None:
            if b == 1:
                for x0, y0, x1, y1, fn in list(self.hitboxes):
                    if x0 <= e.x <= x1 and y0 <= e.y <= y1:
                        fn()
                        return
            self.ui_click(e.x, e.y, b, bool(getattr(e, "state", 0) & 1))
            return
        if b == 3:
            v = self.ent_at_mouse("villager")
            if v is not None:
                self.open_ui("trade", v)
                return
            tx, ty = self.mouse_tile()
            if 0 <= tx < self.W and 0 <= ty < WORLD_H and self.in_reach(tx, ty):
                blk = self.world[ty][tx]
                if blk == TABLE:
                    self.open_ui("table")
                    return
                if blk == ENCHANT_TABLE:
                    self.open_ui("enchant")
                    return
                if blk == FURNACE:
                    self.open_ui("furnace", (tx, ty))
                    return
            st = self.slots[self.selected]
            if st and st[0] == LIGHTER:
                self.try_light()
                return
            if st and st[0] in FOOD:
                self.eat_slot(self.selected)
                return
            if st and st[0] in ARMOR:
                self.equip_slot(self.selected)
                return
        self.buttons.add(b)

    def wheel(self, d):
        if self.scene != "play" or self.paused or self.dead:
            return
        if self.ui in ("creative", "trade", "book"):
            self.scroll_off = max(0, self.scroll_off + d)
            return
        if self.ui is not None:
            return
        self.selected = (self.selected + d) % HB

    # =====================================================================
    # игрок
    # =====================================================================
    def camera(self):
        cx = self.px + PW / 2 - VIEW_W / 2
        cy = self.py + PH / 2 - VIEW_H / 2
        cx = max(0, min(self.W - VIEW_W, cx))
        cy = max(0, min(WORLD_H - VIEW_H, cy))
        return cx, cy

    def in_reach(self, tx, ty):
        dx = tx + 0.5 - (self.px + PW / 2)
        dy = ty + 0.5 - (self.py + PH / 2)
        return math.hypot(dx, dy) <= REACH

    def hurt(self, n, src_x=None, ignore_inv=False, armor=True, cause=""):
        if self.mode == "creative" or self.dead:
            return
        if self.inv_t > 0 and not ignore_inv:
            return
        n = n * DMG_MULT[self.mode]
        if armor:
            pts = self.armor_points()
            if pts > 0:
                self.wear_armor(n)
                n = n * (1 - 0.04 * pts)
        n = max(1, int(round(n)))
        self.hp -= n
        self.inv_t = 40
        if cause:
            self.cause = cause
        if src_x is not None:
            self.kbx = 0.12 if self.px + PW / 2 > src_x else -0.12
            if self.on_ground:
                self.vy = -0.15
        if self.hp <= 0:
            self.die()

    def die(self):
        """Смерть: показываем экран с причиной (в хардкоре мир удаляется)."""
        if self.dead:
            return
        self.dead = True
        self.hp = 0
        self.close_ui()
        self.keys.clear()
        self.buttons.clear()
        self.mining = None
        if self.mode == "hardcore":
            self.delete_files(self.slot)

    def respawn(self):
        self.dead = False
        if self.dim != "over":
            self.switch_dim("over")
        self.hp = MAXHP
        self.food = 20.0
        self.inv_t = 120
        self.ents = [e for e in self.ents if e.kind not in HOSTILES]
        self.arrows = []
        self.px = SPAWN_X + 0.15
        self.py = self.spawn_ground - PH - 0.01
        self.clear_spawn()
        self.vx = self.vy = 0.0
        self.kbx = 0.0
        self.fall_top = None
        self.charge = 0
        self.say("Ты возродился на спавне. Вещи сохранены.", 240)

    def leave_after_death(self):
        hard = self.mode == "hardcore"
        self.exit_to_menu()
        self.dead = False
        self.save_msg = "Хардкор-мир удалён навсегда." if hard else ""

    def attack(self, e):
        creative = self.mode == "creative"
        bt = self.best_tool("sword")
        dmg = 100 if creative else 2
        knock = 0.14
        if bt and not creative:
            st = self.slots[bt[2]]
            dmg = bt[0] + ench_level(st, "sharpness")
            knock += 0.08 * ench_level(st, "knockback")
        self.atk = 18
        self.damage_ent(e, dmg, self.px + PW / 2, knock)
        if bt and not creative:
            self.wear_tool(bt[2])
        self.exh += 0.04

    def damage_ent(self, e, dmg, src_x, knock=0.14):
        e.hp -= dmg
        e.hurt = 10
        e.kb = 12
        e.vx = knock if e.x + e.w / 2 > src_x else -knock
        if e.on_ground or MOBS[e.kind].get("fly"):
            e.vy = -0.15
        if e.kind == "pigman":
            self.anger_pigmen(e)
        if e.hp <= 0 and not e.nodrop:
            parts = []
            for item, lo, hi in MOB_DROPS.get(e.kind, []):
                n = random.randint(lo, hi)
                if n > 0 and self.can_add(item, n):
                    self.add(item, n)
                    parts.append(f"+{n} {NAMES[item]}")
            if parts:
                self.say(", ".join(parts), 80)
            self.add_xp(MOB_XP.get(e.kind, 0))

    def anger_pigmen(self, e):
        e.angry = True
        for o in self.ents:
            if o.kind == "pigman" and math.hypot(o.x - e.x, o.y - e.y) < 14:
                o.angry = True

    def dig(self):
        tx, ty = self.mouse_tile()
        if not (0 <= tx < self.W and 0 <= ty < WORLD_H) or not self.in_reach(tx, ty):
            self.mining = None
            return
        b = self.world[ty][tx]
        if b == AIR or b == LAVA:
            self.mining = None
            return
        if b == BEDROCK:
            self.say("Бедрок невозможно сломать", 60)
            self.mining = None
            return
        if self.mining is None or (self.mining[0], self.mining[1]) != (tx, ty):
            res = self.mine_time(b)
            if res is None:
                self.say(TIER_REQ[NEED_TIER[b]], 70)
                self.mining = None
                return
            self.mining = [tx, ty, 0, res[0], res[1]]
        m = self.mining
        m[2] += 1
        if m[2] >= m[3]:
            creative = self.mode == "creative"
            tool = self.slots[m[4]] if m[4] is not None else None
            silk = ench_level(tool, "silk") > 0
            fort = ench_level(tool, "fortune")
            drop = b if silk else DROPS.get(b, b)
            n = 1
            if fort and not silk and b in ORE_XP:
                n += sum(1 for _ in range(fort) if random.random() < 0.4)
            if not creative and drop and not self.can_add(drop, n):
                self.say("Инвентарь полон!", 60)
                m[2] = m[3] - 1
                return
            self.world[ty][tx] = AIR
            if b == FURNACE:
                self.drop_furnace((tx, ty), creative)
            if not creative:
                if drop:
                    self.add(drop, n)
                    if drop not in BLOCKS:
                        self.say(f"+{n} {NAMES[drop]}", 50)
                if b in (LEAVES, SPRUCE_LEAVES, JUNGLE_LEAVES):
                    if random.random() < 0.06 and self.can_add(APPLE, 1):
                        self.add(APPLE, 1)
                        self.say("+1 Яблоко", 50)
                    elif random.random() < 0.15 and self.can_add(STICK, 1):
                        self.add(STICK, 1)
                if not silk:
                    self.add_xp(ORE_XP.get(b, 0))
                if m[4] is not None:
                    self.wear_tool(m[4])
                self.exh += 0.02
            self.mining = None

    def place(self, tx, ty):
        st = self.slots[self.selected]
        if st is None or st[0] not in PLACEABLE:
            return
        b = st[0]
        self.world[ty][tx] = b
        if self.collides(self.px, self.py):   # нельзя замуровать себя
            self.world[ty][tx] = AIR
            return
        if self.mode != "creative":
            st[1] -= 1
            if st[1] <= 0:
                self.slots[self.selected] = None
        self.pcool = 8

    def player_in(self, block, pad=0.0):
        for ty in range(math.floor(self.py - pad), math.floor(self.py + PH + pad - 1e-9) + 1):
            for tx in range(math.floor(self.px - pad), math.floor(self.px + PW + pad - 1e-9) + 1):
                if self.get(tx, ty) == block:
                    return True
        return False

    def update_player(self):
        keys = set() if self.ui is not None else self.keys
        was_ground = self.on_ground
        creative = self.mode == "creative"
        in_lava = self.player_in(LAVA)
        sp = SPEED * (1.5 if creative else 1.0) * (0.5 if in_lava else 1.0)

        self.vx = 0
        if "left" in keys:
            self.vx -= sp
        if "right" in keys:
            self.vx += sp
        self.vx += self.kbx
        self.kbx *= 0.85
        if abs(self.kbx) < 0.004:
            self.kbx = 0
        if creative:
            self.vy = -0.2 if "jump" in keys else (0.2 if "down" in keys else 0.0)
        elif in_lava:
            self.vy = min(self.vy + GRAVITY * 0.3, 0.08)
            if "jump" in keys:
                self.vy = -0.1
        else:
            if "jump" in keys and self.on_ground:
                self.vy = JUMP_V
                self.exh += 0.03
            self.vy = min(self.vy + GRAVITY, MAX_FALL)

        self.px += self.vx
        if self.collides(self.px, self.py):
            if self.vx > 0:
                self.px = math.floor(self.px + PW) - PW - 0.001
            elif self.vx < 0:
                self.px = math.floor(self.px) + 1.001

        self.py += self.vy
        self.on_ground = False
        if self.collides(self.px, self.py):
            if self.vy > 0:
                self.py = math.floor(self.py + PH) - PH - 0.001
                self.on_ground = True
            elif self.vy < 0:
                self.py = math.floor(self.py) + 1.001
            self.vy = 0

        # урон от падения
        if creative:
            self.fall_top = None
        elif self.on_ground:
            if not was_ground and self.fall_top is not None:
                fall = self.py - self.fall_top
                if fall > 3.6:
                    ff = ench_level(self.armor[3], "feather")
                    dmg = int((fall - 3) * (1 - 0.12 * ff))
                    if dmg > 0:
                        self.hurt(dmg, None, True, False, "Ты разбился при падении")
            self.fall_top = None
        elif self.fall_top is None or self.py < self.fall_top:
            self.fall_top = self.py

        # лава, кактусы
        if in_lava and not creative:
            self.lava_t += 1
            if self.lava_t % 25 == 1:
                self.hurt(4, None, True, False, "Ты сгорел в лаве")
        else:
            self.lava_t = 0
        if not creative and self.player_in(CACTUS, 0.06):
            self.hurt(1, None, False, True, "Тебя уколол кактус")

        # портал
        if self.player_in(PORTAL):
            if not self.portal_lock:
                self.portal_t += 1
                if self.portal_t >= 90:
                    self.travel()
        else:
            self.portal_lock = False
            self.portal_t = max(0, self.portal_t - 2)

    # =====================================================================
    # мобы
    # =====================================================================
    def explode_at(self, cx, cy, r, maxdmg, cause, spare=(BEDROCK, OBSIDIAN, PORTAL)):
        icx, icy = int(cx), int(cy)
        keep = (AIR, LAVA) + tuple(spare)
        for dy in range(-r, r + 1):
            for dx in range(-r, r + 1):
                if dx * dx + dy * dy <= r * r + 1:
                    tx, ty = icx + dx, icy + dy
                    if 0 <= tx < self.W and 0 <= ty < WORLD_H - 1 and self.world[ty][tx] not in keep:
                        self.world[ty][tx] = AIR
        d = math.hypot(self.px + PW / 2 - cx, self.py + PH / 2 - cy)
        rad = r + 2
        if d < rad:
            self.hurt(max(2, int(maxdmg * (1 - d / rad))), cx, True, True, cause)

    def explode(self, e):
        self.explode_at(e.x + e.w / 2, e.y + e.h / 2, 3, 10, "Тебя взорвал крипер")
        e.hp = 0
        e.nodrop = True

    def shoot(self, e):
        sx, sy = e.x + e.w / 2, e.y + 0.5
        dx = self.px + PW / 2 - sx
        dy = self.py + PH / 2 - sy
        d = max(0.1, math.hypot(dx, dy))
        self.arrows.append([sx, sy, dx / d * 0.35, dy / d * 0.35 - 0.02, 160, "e", 3, 0.004])

    def shoot_fire(self, e):
        sx, sy = e.x + e.w / 2, e.y + e.h / 2
        dx = self.px + PW / 2 - sx
        dy = self.py + PH / 2 - sy
        d = max(0.1, math.hypot(dx, dy))
        self.arrows.append([sx, sy, dx / d * 0.18, dy / d * 0.18, 400, "f", 6, 0.0])

    def update_arrows(self):
        keep = []
        for a in self.arrows:
            x, y, vx, vy, life, kind, dmg, g = a
            sp = math.hypot(vx, vy)
            n = max(1, int(sp / 0.2) + 1)
            alive = True
            for _ in range(n):
                x += vx / n
                y += vy / n
                b = self.get(math.floor(x), math.floor(y))
                if b != AIR and b not in PASSABLE:
                    if kind == "f":
                        self.explode_at(x - vx, y - vy, 2, 8, "Тебя сжёг гаст")
                    alive = False
                    break
                if kind == "p":
                    for e in self.ents:
                        if (e.kind != "villager" and e.hp > 0 and e.x <= x <= e.x + e.w
                                and e.y <= y <= e.y + e.h):
                            self.damage_ent(e, dmg, x - vx * 10, 0.12)
                            alive = False
                            break
                    if not alive:
                        break
                elif self.px <= x <= self.px + PW and self.py <= y <= self.py + PH:
                    if kind == "f":
                        self.explode_at(x, y, 2, 8, "Тебя сжёг гаст")
                    else:
                        self.hurt(dmg, x - vx * 5, False, True, "Тебя застрелил скелет")
                    alive = False
                    break
            vy += g
            life -= 1
            if alive and life > 0:
                a[:] = [x, y, vx, vy, life, kind, dmg, g]
                keep.append(a)
        self.arrows = keep

    # ---------- лук ----------
    def aim_vec(self):
        sx = self.px + PW / 2
        sy = self.py + 0.7
        mx, my = self.mouse_world()
        dx, dy = mx - sx, my - sy
        d = math.hypot(dx, dy)
        if d < 0.2:
            dx, dy, d = 1.0, 0.0, 1.0
        return sx, sy, dx / d, dy / d

    def bow_speed(self):
        p = min(1.0, self.charge / BOW_FULL)
        return 0.18 + 0.62 * p

    def sim_arrow(self, sx, sy, vx, vy, g, steps=140):
        """Траектория стрелы: (точки по кадрам, место удара или None)."""
        pts = []
        x, y = sx, sy
        for _ in range(steps):
            n = max(1, int(math.hypot(vx, vy) / 0.2) + 1)
            for _ in range(n):
                x += vx / n
                y += vy / n
                b = self.get(math.floor(x), math.floor(y))
                if b != AIR and b not in PASSABLE:
                    return pts, (x, y)
            vy += g
            pts.append((x, y))
        return pts, None

    def fire_bow(self):
        ch = self.charge
        self.charge = 0
        st = self.slots[self.selected]
        if not st or st[0] != BOW or ch < 6 or self.ui is not None:
            return
        creative = self.mode == "creative"
        if not creative and self.have(ARROW) <= 0:
            self.say("Нет стрел! (стрелы: булыжник + палка + листва)", 90)
            return
        inf = ench_level(st, "infinity") > 0
        if not creative and not inf:
            self.take(ARROW, 1)
        p = min(1.0, ch / BOW_FULL)
        sp = 0.18 + 0.62 * p
        sx, sy, dx, dy = self.aim_vec()
        pw = ench_level(st, "power")
        dmg = (3 + 7 * p) * ((1 + 0.25 * (pw + 1)) if pw else 1.0)
        self.arrows.append([sx, sy, dx * sp, dy * sp, 400, "p", dmg, ARROW_G])
        self.wear_tool(self.selected)
        self.exh += 0.02

    def draw_bow_aim(self, cx, cy):
        c = self.canvas
        sx, sy, dx, dy = self.aim_vec()
        sp = self.bow_speed()
        pts, hit = self.sim_arrow(sx, sy, dx * sp, dy * sp, ARROW_G, 120)
        full = self.charge >= BOW_FULL
        colr = "#ffe066" if full else "#ffffff"
        for i, (x, y) in enumerate(pts):
            if i % 3 == 0:
                px_, py_ = (x - cx) * TILE, (y - cy) * TILE
                r = 3 if i % 6 == 0 else 2
                c.create_oval(px_ - r, py_ - r, px_ + r, py_ + r, fill=colr, outline="#222222")
        if hit:
            hx, hy = (hit[0] - cx) * TILE, (hit[1] - cy) * TILE
            c.create_line(hx - 6, hy - 6, hx + 6, hy + 6, fill="#ff4040", width=3)
            c.create_line(hx - 6, hy + 6, hx + 6, hy - 6, fill="#ff4040", width=3)
        # лук рядом с игроком
        bx, by = (sx - cx) * TILE, (sy - cy) * TILE
        ax, ay = dx, dy
        nx, ny = -ay, ax
        ox, oy = bx + ax * 24, by + ay * 24
        pull = min(1.0, self.charge / BOW_FULL)
        p1 = (ox + nx * 18, oy + ny * 18)
        p2 = (ox + ax * 8, oy + ay * 8)
        p3 = (ox - nx * 18, oy - ny * 18)
        c.create_line(*p1, *p2, *p3, smooth=True, fill="#8b5a2b", width=4)
        mid = (ox - ax * 14 * pull, oy - ay * 14 * pull)
        c.create_line(*p1, *mid, *p3, fill="#eeeeee", width=1)
        c.create_line(*mid, ox + ax * 22, oy + ay * 22, fill="#cccccc", width=2)
        # шкала натяжения над головой
        px0, py0 = (self.px + PW / 2 - cx) * TILE, (self.py - cy) * TILE - 12
        c.create_rectangle(px0 - 16, py0, px0 + 16, py0 + 5, fill="#222222", outline="")
        c.create_rectangle(px0 - 16, py0, px0 - 16 + 32 * pull, py0 + 5,
                           fill="#ffe066" if full else "#8fd0ff", outline="")

    def ai_wander(self, e, sp):
        e.timer -= 1
        if e.timer <= 0:
            e.timer = random.randint(60, 200)
            e.dir = random.choice([-1, 0, 0, 1])
            if e.kind == "villager":
                if e.x - e.home > 8:
                    e.dir = -1
                elif e.home - e.x > 8:
                    e.dir = 1
        if e.kb <= 0:
            e.vx = e.dir * sp
        if e.blocked and e.on_ground and e.dir != 0:
            e.vy = JUMP_V

    def ai_ghast(self, e, dx, dy):
        dist = math.hypot(dx, dy)
        sgn = 1 if dx > 0 else -1
        if e.kb > 0:
            e.vx *= 0.92
            return
        if dist < 32:
            if dist > 14:
                e.vx = sgn * 0.025
            elif dist < 9:
                e.vx = -sgn * 0.025
            else:
                e.vx = 0.0
            want = (self.py - 3) - e.y
            e.vy = max(-0.03, min(0.03, want * 0.01))
            if e.cool <= 0 and dist < 28:
                self.shoot_fire(e)
                e.cool = 140
        else:
            e.timer -= 1
            if e.timer <= 0:
                e.timer = random.randint(60, 200)
                e.dir = random.choice([-1, 0, 1])
                e.vy = random.choice([-0.01, 0.0, 0.01])
            e.vx = e.dir * 0.012

    def ai_hostile(self, e, sp):
        dx = self.px + PW / 2 - (e.x + e.w / 2)
        dy = self.py + PH / 2 - (e.y + e.h / 2)
        dist = abs(dx)
        sgn = 1 if dx > 0 else -1
        chasing = dist < 18 and abs(dy) < 8
        if e.kind == "ghast":
            self.ai_ghast(e, dx, dy)
            return
        if e.kb > 0:
            e.vx *= 0.92
        else:
            if e.kind == "zombie":
                if chasing:
                    e.vx = sgn * sp
                else:
                    self.idle_walk(e, sp)
                if abs(dx) < 0.9 and abs(dy) < 1.4 and e.cool <= 0:
                    self.hurt(3, e.x + e.w / 2, False, True, "Тебя убил зомби")
                    e.cool = 60
            elif e.kind == "pigman":
                if e.angry and chasing:
                    e.vx = sgn * sp * 1.5
                    if abs(dx) < 0.9 and abs(dy) < 1.4 and e.cool <= 0:
                        self.hurt(4, e.x + e.w / 2, False, True, "Тебя убил свинозомби")
                        e.cool = 50
                else:
                    self.idle_walk(e, sp)
            elif e.kind == "skeleton":
                if chasing:
                    if dist < 5:
                        e.vx = -sgn * sp
                    elif dist > 9:
                        e.vx = sgn * sp
                    else:
                        e.vx = 0
                    if e.cool <= 0 and dist < 14:
                        self.shoot(e)
                        e.cool = 100
                else:
                    self.idle_walk(e, sp)
            elif e.kind == "creeper":
                if chasing:
                    if dist < 2.2 and abs(dy) < 2:
                        e.vx = 0
                        e.fuse += 1
                        if e.fuse >= 45:
                            self.explode(e)
                            return
                    else:
                        e.vx = sgn * sp
                        e.fuse = max(0, e.fuse - 2)
                else:
                    e.fuse = 0
                    self.idle_walk(e, sp)
        if e.blocked and e.on_ground and e.vx != 0:
            e.vy = JUMP_V

    def idle_walk(self, e, sp):
        e.timer -= 1
        if e.timer <= 0:
            e.timer = random.randint(60, 200)
            e.dir = random.choice([-1, 0, 1])
        e.vx = e.dir * sp * 0.5

    def update_ent(self, e):
        spec = MOBS[e.kind]
        if e.cool > 0:
            e.cool -= 1
        if e.hurt > 0:
            e.hurt -= 1
        if spec["hostile"]:
            self.ai_hostile(e, spec["speed"])
            if e.hp <= 0:
                return
            # днём зомби и скелеты горят на солнце
            if (self.light > 0.55 and e.kind != "creeper"
                    and not self.covered(int(e.x + e.w / 2), int(e.y))):
                e.hp -= 0.05
                e.nodrop = True
        else:
            self.ai_wander(e, spec["speed"])
        if e.kb > 0:
            e.kb -= 1
        self.move(e)
        if e.vx > 0.001:
            e.face = 1
        elif e.vx < -0.001:
            e.face = -1

    def update_ents(self):
        keep = []
        for e in self.ents:
            far = abs(e.x - self.px)
            if far > SIM_R:
                if e.kind in HOSTILES and far > SIM_R + 10:
                    continue  # мобы далеко от игрока исчезают
                keep.append(e)
                continue
            self.update_ent(e)
            if e.hp > 0:
                keep.append(e)
        self.ents = keep

    def try_spawn_nether(self):
        if sum(1 for e in self.ents if e.kind in ("pigman", "ghast")) >= 8:
            return
        x = int(self.px + random.choice([-1, 1]) * random.randint(14, 30))
        if not 4 <= x < self.W - 4:
            return
        if random.random() < 0.3:
            if sum(1 for e in self.ents if e.kind == "ghast") >= 2:
                return
            y = random.randint(self.top[x] + 8, 82)
            if all(self.get(x + dx, y + dy) == AIR for dx in (-1, 0, 1, 2) for dy in (-1, 0, 1, 2)):
                self.ents.append(Ent("ghast", x, y))
            return
        ys = list(range(int(self.py) - 12, int(self.py) + 13))
        random.shuffle(ys)
        solid = (NETHERRACK, SOUL_SAND, GLOWSTONE, QUARTZ_ORE, NETHER_GOLD, OBSIDIAN)
        for y in ys:
            if y < 4 or y >= WORLD_H - 4:
                continue
            if (self.get(x, y) == AIR and self.get(x, y - 1) == AIR
                    and self.get(x, y + 1) in solid):
                self.ents.append(Ent("pigman", x + 0.15, y + 1 - 1.8 - 0.01))
                return

    def try_spawn(self):
        if self.spawn_t > 0:
            self.spawn_t -= 1
            return
        self.spawn_t = 120
        if self.mode in ("creative", "peaceful"):
            return
        if self.dim == "nether":
            self.try_spawn_nether()
            return
        if sum(1 for e in self.ents if e.kind in HOSTILES) >= (9 if self.mode == "hardcore" else 5):
            return
        x = int(self.px + random.choice([-1, 1]) * random.randint(14, 26))
        if not 2 <= x < self.W - 2:
            return
        if any(a - 8 <= x <= b + 8 for a, b in self.village_spans):
            return
        night = self.light < 0.3
        ys = list(range(int(self.py) - 12, int(self.py) + 13))
        random.shuffle(ys)
        for y in ys:
            if y < 1 or y >= WORLD_H - 2:
                continue
            if (self.get(x, y) == AIR and self.get(x, y - 1) == AIR
                    and self.get(x, y + 1) not in (AIR,)):
                if night or (self.covered(x, y) and y > self.top[x] + 6):
                    kind = random.choice(["zombie", "zombie", "skeleton", "creeper"])
                    h = MOBS[kind]["h"]
                    self.ents.append(Ent(kind, x + 0.15, y + 1 - h - 0.01))
                return

    # =====================================================================
    # главный шаг игры
    # =====================================================================
    def update(self):
        self.time += 1
        if self.dim == "nether":
            self.light = 0.25
        else:
            phase = (self.time % DAY_FRAMES) / DAY_FRAMES
            self.light = max(0.0, min(1.0, 0.5 + math.cos(2 * math.pi * (phase - 0.25))))

        if self.msg_t > 0:
            self.msg_t -= 1
        if self.inv_t > 0:
            self.inv_t -= 1
        if self.atk > 0:
            self.atk -= 1
        if self.pcool > 0:
            self.pcool -= 1

        self.update_furnaces()
        self.update_player()
        self.update_hunger()
        if self.scene != "play" or self.dead:
            return
        self.autosave_t -= 1
        if self.autosave_t <= 0:
            if self.ui is None and self.cursor is None:
                self.autosave_t = 60 * 120
                if self.save_game():
                    self.say("Автосохранение", 70)
            else:
                self.autosave_t = 120
        self.update_ents()
        self.update_arrows()
        self.try_spawn()

        # окна закрываются, если отошёл от верстака, печи или жителя
        pcx, pcy = self.px + PW / 2, self.py + PH / 2
        if self.ui == "furnace" and self.ui_data:
            if math.hypot(self.ui_data[0] + 0.5 - pcx, self.ui_data[1] + 0.5 - pcy) > 7:
                self.close_ui()
        elif self.ui == "table" and not self.near(TABLE, 7):
            self.close_ui()
        elif self.ui == "enchant" and not self.near(ENCHANT_TABLE, 7):
            self.close_ui()
        elif self.ui == "trade" and self.ui_data is not None:
            v = self.ui_data
            if math.hypot(v.x - self.px, v.y - self.py) > 8 or v.hp <= 0:
                self.close_ui()

        # лук, ломать, бить, ставить
        held = self.slots[self.selected]
        bow = bool(held and held[0] == BOW)
        if self.ui is None:
            if bow:
                self.mining = None
                if 1 in self.buttons:
                    self.charge = min(BOW_FULL + 12, self.charge + 1)
                else:
                    self.charge = 0
            else:
                self.charge = 0
                if 1 in self.buttons:
                    target = self.ent_at_mouse("mob")
                    if target is not None:
                        self.mining = None
                        if self.atk == 0:
                            self.attack(target)
                    else:
                        self.dig()
                else:
                    self.mining = None
            if 3 in self.buttons and self.pcool == 0:
                tx, ty = self.mouse_tile()
                if (0 <= tx < self.W and 0 <= ty < WORLD_H and self.in_reach(tx, ty)
                        and self.world[ty][tx] in (AIR, LAVA)):
                    self.place(tx, ty)
        else:
            self.charge = 0

    # =====================================================================
    # отрисовка
    # =====================================================================
    def label(self, x, y, text, anchor="nw", size=10, bold=False):
        font = ("Arial", size, "bold" if bold else "normal")
        self.canvas.create_text(x + 1, y + 1, text=text, anchor=anchor,
                                fill="black", font=font)
        self.canvas.create_text(x, y, text=text, anchor=anchor,
                                fill="white", font=font)

    def draw_block(self, b, sx, sy, tx, ty, lvl):
        c = self.canvas
        if b == LAVA:
            col = "#ff6a00" if ((self.anim // 12) + tx + ty) % 2 == 0 else "#ff8c1a"
            c.create_rectangle(sx, sy, sx + TILE, sy + TILE, fill=col, outline="#c04a00")
            return
        if b == PORTAL:
            col = "#8a2be2" if ((self.anim // 6) + ty) % 2 == 0 else "#b266ff"
            c.create_rectangle(sx, sy, sx + TILE, sy + TILE, fill=col, outline="#5a1a9a")
            return
        c.create_rectangle(sx, sy, sx + TILE, sy + TILE,
                           fill=shade(COLORS[b], lvl), outline="#222222")
        if b in ORE_DOTS:
            dot = ORE_DOTS[b]
            for ox, oy in ((5, 5), (18, 8), (9, 19), (21, 21)):
                ox2 = ox + (tx * 7 + ty * 3) % 4
                oy2 = oy + (tx * 5 + ty * 11) % 3
                c.create_rectangle(sx + ox2, sy + oy2, sx + ox2 + 6, sy + oy2 + 6,
                                   fill=dot, outline="")
        elif b == TABLE:
            c.create_rectangle(sx, sy, sx + TILE, sy + 9,
                               fill=shade("#d19a58", lvl), outline="#222222")
            c.create_rectangle(sx + 3, sy + 12, sx + 9, sy + TILE - 2,
                               fill=shade("#6b4423", lvl), outline="")
            c.create_rectangle(sx + TILE - 9, sy + 12, sx + TILE - 3, sy + TILE - 2,
                               fill=shade("#6b4423", lvl), outline="")
        elif b == ENCHANT_TABLE:
            c.create_rectangle(sx, sy, sx + TILE, sy + 10, fill="#8a1c2a", outline="#222222")
            c.create_rectangle(sx + 8, sy + 2, sx + 24, sy + 8, fill="#f0e0b0", outline="")
            for ox in (4, 14, 24):
                c.create_rectangle(sx + ox, sy + 16, sx + ox + 4, sy + 20, fill="#4be0e0", outline="")
        elif b == CACTUS:
            for ox in (8, 16, 24):
                c.create_line(sx + ox, sy + 4, sx + ox, sy + TILE - 4, fill="#a6d6a6", width=1)
        elif b == GLOWSTONE:
            for ox, oy in ((6, 6), (18, 10), (10, 20), (22, 22)):
                c.create_rectangle(sx + ox, sy + oy, sx + ox + 4, sy + oy + 4, fill="#fff3b0", outline="")
        elif b == FURNACE:
            c.create_rectangle(sx + 7, sy + 12, sx + TILE - 7, sy + TILE - 5,
                               fill="#111111", outline="")
            fs = self.furnaces.get((tx, ty))
            if fs and fs["burn"] > 0:
                c.create_rectangle(sx + 11, sy + 17, sx + TILE - 11, sy + TILE - 7,
                                   fill="#ff8a1f", outline="")

    def draw_ent(self, e, cx, cy):
        c = self.canvas
        sx = (e.x - cx) * TILE
        sy = (e.y - cy) * TILE
        w, h = e.w * TILE, e.h * TILE
        if sx > CW + 40 or sx < -80 or sy > CH + 40 or sy < -80:
            return
        body, head = ENT_COLORS[e.kind]
        if e.kind == "villager":
            body = PROFS[e.prof][1]
        if e.hurt > 0:
            body = head = "#ff6b6b"
        if e.kind == "creeper" and e.fuse > 0 and (e.fuse // 4) % 2 == 0:
            body = head = "#ffffff"
        f = e.face

        if e.kind == "ghast":
            c.create_rectangle(sx, sy, sx + w, sy + h, fill=body, outline="#999999")
            c.create_rectangle(sx + w * 0.18, sy + h * 0.35, sx + w * 0.4, sy + h * 0.5, fill="#222222", outline="")
            c.create_rectangle(sx + w * 0.6, sy + h * 0.35, sx + w * 0.82, sy + h * 0.5, fill="#222222", outline="")
            c.create_rectangle(sx + w * 0.33, sy + h * 0.65, sx + w * 0.67, sy + h * 0.8, fill="#222222", outline="")
            for kk in range(4):
                tx_ = sx + w * (0.15 + 0.23 * kk)
                c.create_line(tx_, sy + h, tx_ + (kk % 2) * 4 - 2, sy + h + 14, fill="#dddddd", width=3)
        elif e.kind == "pig":
            c.create_rectangle(sx, sy + 0.2 * TILE, sx + w, sy + h, fill=body, outline="black")
            hx = sx + w - 0.4 * TILE if f > 0 else sx
            c.create_rectangle(hx, sy, hx + 0.4 * TILE, sy + 0.5 * TILE, fill=head, outline="black")
            nx = hx + 0.4 * TILE if f > 0 else hx - 5
            c.create_rectangle(nx, sy + 0.25 * TILE, nx + 5, sy + 0.45 * TILE,
                               fill="#e88aa0", outline="black")
            ex = hx + (0.25 if f > 0 else 0.1) * TILE
            c.create_rectangle(ex, sy + 0.1 * TILE, ex + 3, sy + 0.1 * TILE + 3,
                               fill="black", outline="")
        else:
            hh = 0.5 * TILE
            if e.kind == "creeper":
                c.create_rectangle(sx, sy, sx + w, sy + h, fill=body, outline="black")
                c.create_rectangle(sx + 4, sy + 5, sx + 9, sy + 11, fill="black", outline="")
                c.create_rectangle(sx + w - 9, sy + 5, sx + w - 4, sy + 11, fill="black", outline="")
                c.create_rectangle(sx + 8, sy + 12, sx + w - 8, sy + 19, fill="black", outline="")
            else:
                c.create_rectangle(sx, sy + hh, sx + w, sy + h, fill=body, outline="black")
                c.create_rectangle(sx + 1, sy, sx + w - 1, sy + hh, fill=head, outline="black")
                ex = sx + w / 2 + f * 0.12 * TILE
                c.create_rectangle(ex - 4, sy + 6, ex - 1, sy + 10, fill="black", outline="")
                c.create_rectangle(ex + 2, sy + 6, ex + 5, sy + 10, fill="black", outline="")
                if e.kind in ("zombie", "pigman"):
                    ax = sx + w if f > 0 else sx - 0.35 * TILE
                    c.create_rectangle(ax, sy + hh + 3, ax + 0.35 * TILE, sy + hh + 9,
                                       fill="#5c9c4a", outline="black")
                elif e.kind == "villager":
                    nx = sx + w / 2 + f * 0.1 * TILE
                    c.create_rectangle(nx - 3, sy + 9, nx + 4, sy + 18,
                                       fill="#b98a63", outline="black")
                elif e.kind == "skeleton":
                    c.create_line(sx + w / 2, sy + hh + 2, sx + w / 2, sy + h - 3,
                                  fill="#888888", width=2)

        if e.kind != "villager" and e.hp < e.maxhp:
            c.create_rectangle(sx, sy - 7, sx + w, sy - 3, fill="#400000", outline="")
            c.create_rectangle(sx, sy - 7, sx + w * max(0, e.hp) / e.maxhp, sy - 3,
                               fill="#e53935", outline="")

    def draw(self):
        if self.scene != "play":
            self.draw_scene()
            return
        c = self.canvas
        c.delete("all")
        cx, cy = self.camera()
        x0, y0 = int(cx), int(cy)
        nether = self.dim == "nether"
        light = self.light
        lvl = 0 if nether else int((1 - light) * 6)

        # небо
        if nether:
            c.configure(bg="#3a0d0d")
        else:
            day, night = (135, 206, 235), (11, 18, 48)
            sky = "#%02x%02x%02x" % tuple(int(night[i] + (day[i] - night[i]) * light) for i in range(3))
            c.configure(bg=sky)
            phase = (self.time % DAY_FRAMES) / DAY_FRAMES
            th = 2 * math.pi * (phase - 0.25)
            sunx = CW / 2 + math.sin(th) * CW * 0.42
            suny = 110 - math.cos(th) * 95
            if suny < 200:
                c.create_oval(sunx - 22, suny - 22, sunx + 22, suny + 22, fill="#ffe94a", outline="")
            moonx = CW / 2 - math.sin(th) * CW * 0.42
            moony = 110 + math.cos(th) * 95
            if moony < 200:
                c.create_oval(moonx - 16, moony - 16, moonx + 16, moony + 16, fill="#e8e8f0", outline="")

        # блоки
        for ty in range(y0, min(WORLD_H, y0 + VIEW_H + 2)):
            row = self.world[ty]
            for tx in range(x0, min(self.W, x0 + VIEW_W + 2)):
                b = row[tx]
                sx = (tx - cx) * TILE
                sy = (ty - cy) * TILE
                if b == AIR:
                    if not nether and ty > self.top[tx] + 1:   # под землёй фон темнее
                        c.create_rectangle(sx, sy, sx + TILE, sy + TILE,
                                           fill="#2b2b33", outline="")
                    continue
                self.draw_block(b, sx, sy, tx, ty, lvl)

        # трещины на ломаемом блоке
        if self.mining:
            mx, my, prog, total = self.mining[:4]
            sx = (mx - cx) * TILE
            sy = (my - cy) * TILE
            for seg in CRACKS[:int(prog / total * 8) + 1]:
                (a, b2), (c2, d) = seg
                c.create_line(sx + a, sy + b2, sx + c2, sy + d, fill="black", width=2)

        # мобы, стрелы
        for e in self.ents:
            if abs(e.x - self.px) < VIEW_W:
                self.draw_ent(e, cx, cy)
        for a in self.arrows:
            ax, ay = (a[0] - cx) * TILE, (a[1] - cy) * TILE
            if a[5] == "f":
                c.create_oval(ax - 7, ay - 7, ax + 7, ay + 7, fill="#ff7a1a", outline="#ffd24a", width=2)
            elif a[5] == "p":
                c.create_line(ax, ay, ax - a[2] * 45, ay - a[3] * 45, fill="#f5f5f5", width=3)
            else:
                c.create_line(ax, ay, ax - a[2] * 40, ay - a[3] * 40, fill="#dddddd", width=2)

        # игрок
        self.draw_player((self.px - cx) * TILE, (self.py - cy) * TILE)

        # лук: траектория и прицел
        held = self.slots[self.selected]
        if (self.ui is None and not self.paused and held and held[0] == BOW):
            if self.charge > 0:
                self.draw_bow_aim(cx, cy)
            mx_, my_ = self.mouse
            c.create_oval(mx_ - 7, my_ - 7, mx_ + 7, my_ + 7, outline="#ffffff", width=2)
            c.create_line(mx_ - 11, my_, mx_ + 11, my_, fill="#ffffff")
            c.create_line(mx_, my_ - 11, mx_, my_ + 11, fill="#ffffff")

        # подсветка под курсором
        if not self.menu_open and not self.paused and not (held and held[0] == BOW):
            tx, ty = self.mouse_tile()
            if self.in_reach(tx, ty):
                sx = (tx - cx) * TILE
                sy = (ty - cy) * TILE
                c.create_rectangle(sx, sy, sx + TILE, sy + TILE, outline="white", width=2)
            v = self.ent_at_mouse("villager")
            if v is not None:
                self.label((v.x + v.w / 2 - cx) * TILE, (v.y - cy) * TILE - 6,
                           f"{PROFS[v.prof][0]} (ПКМ - торговля)", anchor="s", bold=True)

        # эффект портала
        if self.portal_t > 0:
            t = min(1.0, self.portal_t / 90.0)
            th_ = int(10 + 190 * t)
            for rect in ((0, 0, CW, th_), (0, CH - th_, CW, CH), (0, 0, th_, CH), (CW - th_, 0, CW, CH)):
                c.create_rectangle(*rect, fill="#6a1bb2" if self.portal_t % 8 < 4 else "#8a2be2",
                                   outline="")

        self.draw_hud()
        self.hitboxes = []
        self.ui_slots = []
        if self.ui is not None:
            self.draw_ui()
        if self.msg_t > 0:
            self.label(CW // 2, CH - 150, self.msg, anchor="center", size=13, bold=True)
        if self.paused:
            self.draw_pause()
        if self.dead:
            self.draw_death()

    def draw_player(self, sx, sy):
        c = self.canvas
        w, h = PW * TILE, PH * TILE
        flash = self.inv_t > 0 and (self.inv_t // 4) % 2 == 0
        ac = [(COLORS[st[0]] if st else None) for st in self.armor]
        shirt = "#ff5555" if flash else (ac[1] or "#3b6fd4")
        pants = "#ff5555" if flash else (ac[2] or "#2c4a8c")
        c.create_rectangle(sx, sy + 0.5 * TILE, sx + w, sy + h, fill=shirt, outline="black", width=2)
        c.create_rectangle(sx, sy + 1.2 * TILE, sx + w, sy + h, fill=pants, outline="black", width=2)
        if ac[3]:
            c.create_rectangle(sx, sy + h - 0.3 * TILE, sx + w, sy + h, fill=ac[3], outline="black", width=2)
        c.create_rectangle(sx + 2, sy + 2, sx + w - 2, sy + 0.5 * TILE, fill="#f1c27d", outline="black")
        if ac[0]:
            c.create_rectangle(sx + 1, sy, sx + w - 1, sy + 0.22 * TILE, fill=ac[0], outline="black")

    def draw_hud(self):
        c = self.canvas
        slot = 44
        hx0 = (CW - slot * HB) // 2
        hy = CH - slot - 8
        hx1 = hx0 + slot * HB - 4

        # хотбар
        for i in range(HB):
            x = hx0 + i * slot
            sel = i == self.selected
            c.create_rectangle(x, hy, x + slot - 4, hy + slot - 4, fill="#444444",
                               outline="yellow" if sel else "#111111", width=3 if sel else 1)
            st = self.slots[i]
            if st:
                self.draw_item(x + 6, hy + 6, slot - 16, st[0])
                if len(st) > 3 and st[3]:
                    self.draw_glint(x + 6, hy + 6, slot - 16)
                if st[1] > 1:
                    c.create_text(x + slot - 7, hy + slot - 7, text=str(st[1]), anchor="se",
                                  fill="white", font=("Arial", 10, "bold"))
                self.draw_dur(x + 6, hy + slot - 12, slot - 16, st)
            c.create_text(x + 3, hy + 2, text=str(i + 1), anchor="nw",
                          fill="#cccccc", font=("Arial", 8))
        st = self.slots[self.selected]
        if st:
            self.label(CW // 2, hy - (64 if self.mode != "creative" else 8),
                       NAMES[st[0]], anchor="s", size=11, bold=True)
            if st[0] == BOW and self.mode != "creative":
                self.label(CW // 2 + 150, hy - 64, f"Стрел: {self.have(ARROW)}",
                           anchor="s", size=10, bold=True)

        if self.mode != "creative":
            # опыт
            need = self.xp_need(self.xp_level)
            c.create_rectangle(hx0, hy - 8, hx1, hy - 3, fill="#12301a", outline="#0a1a0a")
            c.create_rectangle(hx0, hy - 8, hx0 + (hx1 - hx0) * self.xp_prog / need, hy - 3,
                               fill="#7cff4a", outline="")
            if self.xp_level > 0:
                c.create_text(CW // 2 + 1, hy - 10, text=str(self.xp_level), anchor="s",
                              fill="black", font=("Arial", 11, "bold"))
                c.create_text(CW // 2, hy - 11, text=str(self.xp_level), anchor="s",
                              fill="#7cff4a", font=("Arial", 11, "bold"))
            # сердца
            for i in range(10):
                full = self.hp >= 2 * i + 2
                half = self.hp == 2 * i + 1
                col = "#e53935" if full else ("#ff9800" if half else "#555555")
                c.create_text(hx0 + i * 17, hy - 40, anchor="nw", text="♥", fill=col,
                              font=("Arial", 15, "bold"))
            # голод
            food = int(self.food)
            for i in range(10):
                v = food - 2 * i
                xr = hx1 - (i + 1) * 17
                col = "#c26a1c" if v >= 2 else ("#8a5a2a" if v == 1 else "#3a3a3a")
                c.create_oval(xr + 1, hy - 37, xr + 15, hy - 23, fill=col, outline="#222222")
                if v >= 2:
                    c.create_rectangle(xr + 10, hy - 26, xr + 16, hy - 21, fill="#eeeeee", outline="")
            # броня
            pts = self.armor_points()
            if pts > 0:
                for i in range(10):
                    v = pts - 2 * i
                    col = "#b0bec5" if v >= 2 else ("#78909c" if v == 1 else "#3a3a3a")
                    c.create_rectangle(hx0 + i * 17 + 1, hy - 58, hx0 + i * 17 + 14, hy - 46,
                                       fill=col, outline="#222222")

        x = min(self.W - 1, max(0, int(self.px)))
        if self.dim == "nether":
            where = "Незер"
            depth_txt = f"X: {x}  (в обычном мире ~{x * PORTAL_RATIO})"
        else:
            where = BIOME_DEFS.get(self.biome[x], {}).get("name", "")
            depth = max(0, int(self.py - self.top[x]))
            depth_txt = f"X: {x}  Глубина: {depth}"
        day = self.time // DAY_FRAMES + 1
        self.label(10, 8, f"{self.name or 'Мир'}  [{MODE_NAMES.get(self.mode, '')}]", size=10, bold=True)
        self.label(10, 26, f"{depth_txt}  День {day}", size=10)
        self.label(10, 44, f"Биом: {where}", size=10)
        if self.have(EMERALD):
            self.label(10, 62, f"Изумруды: {self.have(EMERALD)}", size=10, bold=True)
        self.label(CW - 10, 8, "E - инвентарь   F - есть   Esc - пауза / сохранение",
                   anchor="ne", size=10)

    # =====================================================================
    # сохранение и загрузка
    # =====================================================================
    def save_path(self, slot):
        return os.path.join(SAVE_DIR, f"world{slot}.json")

    def meta_path(self, slot):
        return os.path.join(SAVE_DIR, f"world{slot}.meta.json")

    def read_metas(self):
        metas = []
        for i in range(1, SLOTS + 1):
            meta = None
            if os.path.exists(self.save_path(i)):
                try:
                    with open(self.meta_path(i), "r", encoding="utf-8") as f:
                        meta = json.load(f)
                except Exception:
                    meta = {"day": "?", "saved": "?"}
            metas.append(meta)
        return metas

    def dim_snapshot(self, st):
        W = st["W"]
        snap = {
            "w": W,
            "world": base64.b64encode(zlib.compress(b"".join(st["world"]), 6)).decode("ascii"),
            "top": st["top"],
            "spans": [list(sp) for sp in st["village_spans"]],
            "ents": [[e.kind, e.x, e.y, e.hp, e.prof, e.home]
                     for e in st["ents"] if e.kind not in HOSTILES and e.hp > 0],
            "furnaces": [[kk[0], kk[1], f["slots"], f["burn"], f["burn_max"], f["cook"]]
                         for kk, f in st["furnaces"].items()],
        }
        if W == WORLD_W:
            snap["biome"] = [BIOMES.index(b) for b in st["biome"]]
        return snap

    def save_game(self):
        try:
            os.makedirs(SAVE_DIR, exist_ok=True)
            dims = {self.dim: self.dim_snapshot(self.pack_dim())}
            for name, st in self.dims.items():
                dims[name] = self.dim_snapshot(st)
            data = {
                "version": 3,
                "name": self.name,
                "mode": self.mode,
                "dim": self.dim,
                "dims": dims,
                "spawn_ground": self.spawn_ground,
                "px": self.px, "py": self.py, "hp": self.hp,
                "food": self.food, "exh": self.exh,
                "selected": self.selected,
                "time": self.time,
                "xp": [self.xp_level, self.xp_prog],
                "ench_seed": self.ench_seed,
                "slots": self.slots,
                "armor": self.armor,
            }
            path = self.save_path(self.slot)
            with open(path + ".tmp", "w", encoding="utf-8") as f:
                json.dump(data, f, separators=(",", ":"))
            os.replace(path + ".tmp", path)
            meta = {"name": self.name, "mode": self.mode,
                    "day": self.time // DAY_FRAMES + 1,
                    "saved": time.strftime("%d.%m.%Y %H:%M")}
            with open(self.meta_path(self.slot), "w", encoding="utf-8") as f:
                json.dump(meta, f)
            self.save_msg = "Игра сохранена в " + time.strftime("%H:%M:%S")
            return True
        except Exception as ex:
            self.save_msg = f"Ошибка сохранения: {ex}"
            return False

    def load_game(self, slot):
        H = WORLD_H
        with open(self.save_path(slot), "r", encoding="utf-8") as f:
            d = json.load(f)
        if d.get("version", 1) < 3 or "dims" not in d:
            raise ValueError("мир создан в старой версии игры (1200 блоков) и здесь не открывается")
        states = {}
        for name, sn in d["dims"].items():
            W = sn["w"]
            raw = zlib.decompress(base64.b64decode(sn["world"]))
            if len(raw) != W * H:
                raise ValueError("файл сохранения повреждён")
            world = [bytearray(raw[y * W:(y + 1) * W]) for y in range(H)]
            biome = [BIOMES[i] for i in sn["biome"]] if "biome" in sn else ["nether"] * W
            ents = []
            for kind, x, y, hp, prof, home in sn["ents"]:
                e = Ent(kind, x, y, prof)
                e.hp = hp
                e.home = home
                ents.append(e)
            furnaces = {}
            for x, y, sl, burn, bmax, cook in sn["furnaces"]:
                furnaces[(x, y)] = {"slots": [fix_stack(st) for st in sl],
                                    "burn": burn, "burn_max": bmax, "cook": cook}
            states[name] = dict(world=world, top=sn["top"], biome=biome,
                                village_spans=[tuple(sp) for sp in sn["spans"]],
                                ents=ents, furnaces=furnaces, arrows=[], W=W)
        self.name = d.get("name", f"Мир {slot}")
        self.mode = d.get("mode", "normal")
        self.init_state()
        cur = d.get("dim", "over")
        self.dims = {k: v for k, v in states.items() if k != cur}
        self.unpack_dim(states[cur])
        self.dim = cur
        self.spawn_ground = d["spawn_ground"]
        self.px, self.py, self.hp = d["px"], d["py"], d["hp"]
        self.food = d.get("food", 20.0)
        self.exh = d.get("exh", 0.0)
        self.selected = min(d.get("selected", 0), HB - 1)
        self.time = d["time"]
        self.xp_level, self.xp_prog = d.get("xp", [0, 0])
        self.ench_seed = d.get("ench_seed", 1)
        sl = [fix_stack(st) for st in d["slots"]]
        self.slots = (sl + [None] * NSLOTS)[:NSLOTS]
        ar = [fix_stack(st) for st in d.get("armor", [])]
        self.armor = (ar + [None] * 4)[:4]

    def start_slot(self, i):
        """Загрузить существующий мир из слота i (1-3)."""
        self.slot = i
        self.confirm_del = None
        self.save_msg = ""
        self.canvas.delete("all")
        self.canvas.configure(bg="#2b2b33")
        self.canvas.create_text(CW // 2, CH // 2, fill="white", font=("Arial", 22, "bold"),
                                text="Загрузка мира...")
        self.root.update()
        try:
            self.load_game(i)
        except Exception as ex:
            self.save_msg = f"Не удалось загрузить мир: {ex}"
            self.scene = "slots"
            return
        self.scene = "play"
        self.paused = False
        self.keys.clear()
        self.buttons.clear()
        self.say("Мир загружен. Esc - пауза и сохранение", 240)
        self.save_msg = ""

    def click_slot(self, i):
        self.confirm_del = None
        if os.path.exists(self.save_path(i)):
            self.start_slot(i)
        else:
            self.create_slot = i
            self.cname = ""
            self.cseed = ""
            self.cmode = 2
            self.cfocus = "name"
            self.scene = "create"

    def set_cmode(self, i):
        self.cmode = i

    def set_focus(self, which):
        self.cfocus = which

    def finish_create(self):
        i = self.create_slot
        name = self.cname.strip() or f"Мир {i}"
        self.create_world(i, name, MODES[self.cmode][0], self.cseed.strip() or None)

    def create_world(self, i, name, mode, seed):
        self.slot = i
        self.name = name
        self.mode = mode
        self.canvas.delete("all")
        self.canvas.configure(bg="#2b2b33")
        self.canvas.create_text(CW // 2, CH // 2, fill="white", font=("Arial", 22, "bold"),
                                text="Генерация мира...")
        self.root.update()
        try:
            self.new_world(seed)
            self.save_game()
        except Exception as ex:
            self.save_msg = f"Не удалось создать мир: {ex}"
            self.scene = "slots"
            return
        self.scene = "play"
        self.paused = False
        self.keys.clear()
        self.buttons.clear()
        self.save_msg = ""

    def create_key(self, e, k):
        if k == "escape":
            self.scene = "slots"
            return
        if k in ("return", "kp_enter"):
            self.finish_create()
            return
        if k == "tab":
            self.cfocus = "seed" if self.cfocus == "name" else "name"
            return
        attr = "cname" if self.cfocus == "name" else "cseed"
        cur = getattr(self, attr)
        if k == "backspace":
            setattr(self, attr, cur[:-1])
        else:
            ch = getattr(e, "char", "")
            if ch and ch.isprintable() and len(cur) < 24:
                setattr(self, attr, cur + ch)

    def delete_files(self, slot):
        for path in (self.save_path(slot), self.meta_path(slot)):
            try:
                os.remove(path)
            except OSError:
                pass

    def delete_slot(self, i):
        if self.confirm_del != i:
            self.confirm_del = i
            return
        self.delete_files(i + 1)
        self.confirm_del = None
        self.metas = self.read_metas()

    def open_pause(self):
        self.paused = True
        self.save_msg = ""
        self.buttons.clear()
        self.keys.clear()
        self.mining = None

    def resume(self):
        self.paused = False

    def save_and_exit(self):
        if self.save_game():
            self.exit_to_menu()

    def exit_to_menu(self):
        self.scene = "slots"
        self.paused = False
        self.dead = False
        self.close_ui()
        self.keys.clear()
        self.buttons.clear()
        self.confirm_del = None
        self.metas = self.read_metas()

    def back_scene(self):
        if self.scene == "slots":
            self.scene = "title"
            self.confirm_del = None
            self.save_msg = ""
        elif self.scene == "create":
            self.scene = "slots"

    def go_slots(self):
        self.metas = self.read_metas()
        self.scene = "slots"

    def on_close(self):
        if self.scene == "play":
            was = self.paused
            self.paused = True
            try:
                from tkinter import messagebox
                ans = messagebox.askyesnocancel("Выход", "Сохранить игру перед выходом?")
            except Exception:
                ans = False
            if ans is None:
                self.paused = was
                return
            if ans:
                self.save_game()
        self.root.destroy()

    # =====================================================================
    # главное меню, выбор слота, пауза
    # =====================================================================
    def button(self, x, y, w, h, text, fn, enabled=True, danger=False):
        c = self.canvas
        mx, my = self.mouse
        hover = enabled and x <= mx <= x + w and y <= my <= y + h
        base = "#555555" if not enabled else "#7a7a7a"
        if hover:
            base = "#b85a5a" if danger else "#6f7fb8"
        c.create_rectangle(x, y, x + w, y + h, fill="#1a1a1a", outline="")
        c.create_rectangle(x + 2, y + 2, x + w - 2, y + h - 2, fill=base, outline="")
        c.create_line(x + 2, y + 2, x + w - 2, y + 2, fill="#c8c8c8", width=2)
        c.create_line(x + 2, y + 2, x + 2, y + h - 2, fill="#c8c8c8", width=2)
        c.create_line(x + 2, y + h - 2, x + w - 2, y + h - 2, fill="#3a3a3a", width=2)
        c.create_line(x + w - 2, y + 2, x + w - 2, y + h - 2, fill="#3a3a3a", width=2)
        self.label(x + w / 2, y + h / 2, text, anchor="center", size=12, bold=True)
        if enabled:
            self.hitboxes.append((x, y, x + w, y + h, fn))

    def draw_backdrop(self):
        c = self.canvas
        c.configure(bg="#6fb4e8")
        off = self.anim * 0.03
        base = int(off)
        frac = off - base
        # облака
        for k in range(4):
            cx = (k * 260 - self.anim * 0.4) % (CW + 240) - 120
            cy = 40 + (k * 37) % 90
            c.create_rectangle(cx, cy, cx + 110, cy + 24, fill="#f4f8ff", outline="")
            c.create_rectangle(cx + 20, cy - 14, cx + 80, cy, fill="#f4f8ff", outline="")
        # ландшафт
        for i in range(VIEW_W + 2):
            wx = base + i
            h = int(11 + 2.5 * math.sin(wx * 0.35) + 1.5 * math.sin(wx * 0.11 + 1))
            sx = (i - frac) * TILE
            for r in range(h, VIEW_H + 1):
                if r == h:
                    col = COLORS[GRASS]
                elif r < h + 4:
                    col = COLORS[DIRT]
                elif (wx * 7 + r * 13) % 11 == 0:
                    col = COLORS[COBBLE]
                else:
                    col = COLORS[STONE]
                c.create_rectangle(sx, r * TILE, sx + TILE, r * TILE + TILE,
                                   fill=shade(col, 1), outline="#2a2a2a")

    def title_text(self, x, y, text, size):
        c = self.canvas
        font = ("Arial", size, "bold")
        for off in (5, 4, 3, 2, 1):
            c.create_text(x + off, y + off, text=text, fill="#3a3a3a", font=font)
        c.create_text(x, y, text=text, fill="#e8e8e8", font=font)

    def text_box(self, x, y, w, h, text, focused, fn, hint=""):
        c = self.canvas
        c.create_rectangle(x, y, x + w, y + h, fill="#101010",
                           outline="#ffffff" if focused else "#777777", width=2)
        blink = "_" if focused and (self.anim // 30) % 2 == 0 else ""
        if text or focused or not hint:
            c.create_text(x + 8, y + h / 2, anchor="w", text=text + blink, fill="#ffffff",
                          font=("Arial", 13))
        else:
            c.create_text(x + 8, y + h / 2, anchor="w", text=hint, fill="#777777",
                          font=("Arial", 13))
        self.hitboxes.append((x, y, x + w, y + h, fn))

    def draw_create(self):
        c = self.canvas
        self.title_text(CW // 2, 46, "Создание мира", 28)
        pw = 520
        x = (CW - pw) // 2
        self.label(x, 88, "Название мира", size=11, bold=True)
        self.text_box(x, 110, pw, 34, self.cname, self.cfocus == "name",
                      lambda: self.set_focus("name"), f"Мир {self.create_slot}")
        self.label(x, 160, "Режим игры", size=11, bold=True)
        bw = (pw - 10) // 2
        for i, (key, nm, desc) in enumerate(MODES):
            bx = x + (i % 2) * (bw + 10)
            by = 182 + (i // 2) * 52
            self.button(bx, by, bw, 44, nm, lambda i=i: self.set_cmode(i))
            if i == self.cmode:
                c.create_rectangle(bx - 3, by - 3, bx + bw + 3, by + 47, outline="#7cff7c", width=3)
        self.label(CW // 2, 296, MODES[self.cmode][2], anchor="center", size=11)
        self.label(x, 322, "Сид мира (необязательно, одинаковый сид - одинаковый мир)", size=11, bold=True)
        self.text_box(x, 344, pw, 34, self.cseed, self.cfocus == "seed",
                      lambda: self.set_focus("seed"), "случайный")
        self.button(CW // 2 - 260, CH - 90, 250, 42, "Создать мир", self.finish_create)
        self.button(CW // 2 + 10, CH - 90, 250, 42, "Отмена", self.back_scene)

    def draw_scene(self):
        c = self.canvas
        c.delete("all")
        self.hitboxes = []
        self.draw_backdrop()
        if self.scene == "title":
            self.title_text(CW // 2, 100, "МАЙНКРАФТ 2D", 46)
            c.create_text(CW // 2 + 2, 152, text=self.splash, fill="black",
                          font=("Arial", 14, "bold"))
            c.create_text(CW // 2, 150, text=self.splash, fill="#ffee33",
                          font=("Arial", 14, "bold"))
            self.button(CW // 2 - 150, 230, 300, 44, "Играть", self.go_slots)
            self.button(CW // 2 - 150, 290, 300, 44, "Выход", self.on_close)
            self.label(CW // 2, CH - 20, "Сохранения хранятся в папке saves рядом с игрой",
                       anchor="center", size=10)
        elif self.scene == "create":
            self.draw_create()
        else:
            self.title_text(CW // 2, 60, "Выбери мир", 28)
            rw, rh = 560, 92
            rx = (CW - rw) // 2
            mx, my = self.mouse
            for i in range(SLOTS):
                ry = 112 + i * (rh + 12)
                meta = self.metas[i]
                hover = rx <= mx <= rx + rw and ry <= my <= ry + rh
                c.create_rectangle(rx, ry, rx + rw, ry + rh,
                                   fill="#3d3d4a" if hover else "#2b2b35",
                                   outline="#dddddd" if hover else "#777777", width=2)
                ix, iy = rx + 14, ry + 14
                if meta:
                    c.create_rectangle(ix, iy, ix + 64, iy + 64, fill="#87ceeb", outline="black")
                    c.create_rectangle(ix, iy + 34, ix + 64, iy + 42, fill=COLORS[GRASS], outline="")
                    c.create_rectangle(ix, iy + 42, ix + 64, iy + 64, fill=COLORS[DIRT], outline="")
                    c.create_rectangle(ix, iy, ix + 64, iy + 64, fill="", outline="black")
                else:
                    c.create_rectangle(ix, iy, ix + 64, iy + 64, fill="#444444", outline="black")
                    c.create_text(ix + 32, iy + 32, text="+", fill="#aaaaaa",
                                  font=("Arial", 30, "bold"))
                if meta:
                    self.label(rx + 96, ry + 14, str(meta.get("name", f"Мир {i + 1}")),
                               size=16, bold=True)
                    mname = MODE_NAMES.get(meta.get("mode", "normal"), "Нормальный")
                    sub = (f"{mname}   День {meta.get('day', '?')}   "
                           f"сохранено: {meta.get('saved', '?')}")
                else:
                    self.label(rx + 96, ry + 14, f"Мир {i + 1}", size=16, bold=True)
                    sub = "Пусто - нажми, чтобы создать новый мир"
                self.label(rx + 96, ry + 48, sub, size=11)
                if meta:
                    sure = self.confirm_del == i
                    self.button(rx + rw - 124, ry + (rh - 34) // 2, 110, 34,
                                "Точно?" if sure else "Удалить",
                                lambda i=i: self.delete_slot(i), danger=True)
                self.hitboxes.append((rx, ry, rx + rw, ry + rh,
                                      lambda i=i: self.click_slot(i + 1)))
            if self.save_msg:
                self.label(CW // 2, CH - 112, self.save_msg, anchor="center", size=11, bold=True)
            self.button(CW // 2 - 150, CH - 90, 300, 40, "Назад", self.back_scene)

    def draw_death(self):
        c = self.canvas
        pw, ph = 480, 270
        x, y = (CW - pw) // 2, 130
        c.create_rectangle(x, y, x + pw, y + ph, fill="#2a0a0a", outline="#cc3333", width=3)
        self.title_text(CW // 2, y + 46, "Ты погиб!", 34)
        self.label(CW // 2, y + 92, self.cause or "Ты умер", anchor="center", size=14, bold=True)
        day = self.time // DAY_FRAMES + 1
        self.label(CW // 2, y + 118, f"Ты прожил до дня {day}", anchor="center", size=11)
        if self.mode == "hardcore":
            self.label(CW // 2, y + 142, "Хардкор: мир удалён навсегда", anchor="center", size=11, bold=True)
            self.button(CW // 2 - 150, y + 180, 300, 42, "Выйти в меню", self.leave_after_death)
        else:
            self.button(CW // 2 - 150, y + 160, 300, 42, "Возродиться", self.respawn)
            self.button(CW // 2 - 150, y + 210, 300, 42, "Выйти в меню (без сохранения)",
                        self.leave_after_death, danger=True)

    def draw_pause(self):
        c = self.canvas
        pw, ph = 380, 310
        x, y = (CW - pw) // 2, 120
        c.create_rectangle(x, y, x + pw, y + ph, fill="#1e1e24", outline="#bbbbbb", width=3)
        self.label(CW // 2, y + 26, "Игра приостановлена", anchor="center", size=15, bold=True)
        bx = x + 30
        self.button(bx, y + 55, 320, 38, "Продолжить", self.resume)
        self.button(bx, y + 103, 320, 38, "Сохранить игру", self.save_game)
        self.button(bx, y + 151, 320, 38, "Сохранить и выйти в меню", self.save_and_exit)
        self.button(bx, y + 199, 320, 38, "Выйти без сохранения", self.exit_to_menu, danger=True)
        if self.save_msg:
            ok = self.save_msg.startswith("Игра сохранена")
            c.create_text(CW // 2, y + 258, text=self.save_msg,
                          fill="#7cff7c" if ok else "#ff7c7c", font=("Arial", 11, "bold"))
        c.create_text(CW // 2, y + 284, fill="#999999", font=("Arial", 9),
                      text="Прогресс сохраняется только кнопкой «Сохранить»")

    # =====================================================================
    def loop(self):
        try:
            now = time.perf_counter()
            self.acc = min(self.acc + now - self.last, 0.1)
            self.last = now
            steps = 0
            while self.acc >= DT and steps < 4:
                self.anim += 1
                if self.scene == "play" and not self.paused and not self.dead:
                    self.update()
                self.acc -= DT
                steps += 1
            if steps:
                self.draw()
        except Exception as ex:
            # одна ошибка не должна останавливать игру
            import traceback
            traceback.print_exc()
            self.mining = None
            self.buttons.clear()
            self.acc = 0.0
            if self.scene == "play":
                self.say(f"Ошибка: {ex}", 180)
        self.root.after(2, self.loop)


if __name__ == "__main__":
    root = tk.Tk()
    Game(root)
    root.mainloop()
