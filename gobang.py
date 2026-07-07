"""
五子棋 — 最终美化版
15×15 棋盘，支持双人对战 / 人机对战，含 3D 棋子、胜利动画等。
"""

import sys
import math
import random
import pygame

# ============================================================
# 常量定义
# ============================================================
WIN_WIDTH, WIN_HEIGHT = 800, 600
FPS = 60

BOARD_SIZE       = 15
CELL_SIZE        = 34
GRID_PIXEL       = (BOARD_SIZE - 1) * CELL_SIZE   # 476
BOARD_AREA_WIDTH = 570
PANEL_START_X    = BOARD_AREA_WIDTH

OFFSET_X = (BOARD_AREA_WIDTH - GRID_PIXEL) // 2    # 47
OFFSET_Y = (WIN_HEIGHT - GRID_PIXEL) // 2          # 62

FRAME_MARGIN = 16
FRAME_DEPTH  = 3

# ── 颜色体系（水墨风） ──
# 宣纸色系
C_PAGE_BG    = (248, 245, 238)   # 左侧 — 宣纸白
C_PANEL_BG   = (242, 238, 228)   # 右侧面板 — 稍深宣纸
C_DIVIDER    = (195, 188, 175)   # 分隔淡墨线

# 边框 — 墨色层次
C_FRAME_DARK  = (40, 36, 32)     # 外框 — 浓墨
C_FRAME_LIGHT = (92, 85, 75)     # 内框 — 中墨
C_BOARD_FACE  = (240, 236, 222)  # 棋盘面 — 淡宣纸
C_WOOD_A      = (236, 231, 216)  # 纸纹浅
C_WOOD_B      = (244, 239, 226)  # 纸纹深

C_GRID        = (68, 63, 54)     # 网格线 — 淡墨
C_STAR        = (48, 44, 38)     # 星位 — 中墨
C_LABEL       = (138, 132, 120)  # 坐标标注 — 浅墨

STONE_RADIUS = CELL_SIZE // 2 - 2  # 15 px
SHADOW_DX, SHADOW_DY = 2, 2
SHADOW_COLOR = (38, 33, 26, 50)

# 按钮色 — 墨韵
BTN_DARK     = (50, 44, 38)      # 主按钮
BTN_DARK_H   = (68, 60, 52)
BTN_MID      = (105, 96, 85)     # 中性按钮
BTN_MID_H    = (125, 114, 102)
BTN_ACCENT   = (162, 58, 48)     # 退出 — 朱砂印色
BTN_ACCENT_H = (182, 72, 58)
BTN_TEXT_C   = (248, 245, 238)   # 按钮文字

# 模式按钮色
MODE_PVP_ACTIVE   = (48, 42, 36)      # 浓墨
MODE_PVP_NORMAL   = (228, 222, 210)   # 淡宣纸
MODE_PVE_ACTIVE   = (82, 76, 66)      # 中墨
MODE_PVE_NORMAL   = (225, 218, 204)   # 淡宣纸

# 难度按钮色
DIFF_EASY_ACTIVE   = (52, 46, 40)
DIFF_EASY_NORMAL   = (228, 222, 210)
DIFF_MEDIUM_ACTIVE = (72, 64, 55)
DIFF_MEDIUM_NORMAL = (225, 218, 204)
DIFF_HARD_ACTIVE   = (158, 55, 45)
DIFF_HARD_NORMAL   = (230, 220, 214)

# 回合徽章色
TURN_BLACK  = (46, 40, 35)
TURN_WHITE  = (105, 98, 85)
TURN_AI     = (75, 68, 58)
TURN_WIN_B  = (40, 34, 28)
TURN_WIN_W  = (98, 92, 80)
TURN_DRAW   = (140, 132, 118)
TURN_TEXT_C = (248, 245, 235)

# 面板文字色
C_TITLE      = (48, 40, 32)      # 标题浓墨
C_LINE       = (195, 188, 172)   # 分隔淡墨
C_SEC_TITLE  = (115, 106, 92)    # 次级标题
C_VALUE      = (68, 60, 48)      # 数值
C_TIP_LABEL  = (92, 82, 68)      # 提示标签
C_TIP_TEXT   = (142, 135, 122)   # 提示文字

# ── 预计算帧矩形 ──
_fx = OFFSET_X - FRAME_MARGIN
_fy = OFFSET_Y - FRAME_MARGIN
_fw = GRID_PIXEL + FRAME_MARGIN * 2
_fh = GRID_PIXEL + FRAME_MARGIN * 2
FRAME_RECT = pygame.Rect(_fx, _fy, _fw, _fh)

# ── 胜利粒子参数 ──
SPARKLE_COUNT = 50
SPARKLE_COLORS = [
    (218, 178, 92), (235, 205, 125), (245, 225, 168),
    (200, 155, 65), (225, 190, 105),
]

# ── 宣纸纹理缓存 ──
_paper_cache = None

# ============================================================
# 游戏状态
# ============================================================
board         = [[0] * BOARD_SIZE for _ in range(BOARD_SIZE)]
current_player = 1
game_over      = False
winner         = 0
move_count     = 0
last_move      = None
win_line       = []
move_history   = []
button_rects   = []
game_mode      = "pvp"
ai_difficulty  = "medium"    # 人机难度: easy / medium / hard
ai_thinking    = False
ai_think_start = 0

# 胜场统计
black_wins = 0
white_wins = 0
draws      = 0

# 胜利动画
victory_sparkles = []       # [x, y, vx, vy, life, max_life]
victory_start_ms = 0
_glow_surf_cache = None     # 胜利棋子光晕（预生成，避免每帧重复创建）

# 悬停
hover_pos = None

# 先后手选择
player_color = 1       # 玩家执棋颜色: 1=黑(先手), 2=白(后手)
game_state = "playing"  # "playing" | "color_select"


# ============================================================
# 辅助函数
# ============================================================
def board_to_pixel(row, col):
    return OFFSET_X + col * CELL_SIZE, OFFSET_Y + row * CELL_SIZE


def pixel_to_board(mx, my):
    col = round((mx - OFFSET_X) / CELL_SIZE)
    row = round((my - OFFSET_Y) / CELL_SIZE)
    if 0 <= row < BOARD_SIZE and 0 <= col < BOARD_SIZE:
        px, py = board_to_pixel(row, col)
        if (mx - px) ** 2 + (my - py) ** 2 <= (CELL_SIZE // 2) ** 2:
            return row, col
    return None


def reset_game():
    global current_player, game_over, winner, move_count, last_move
    global win_line, move_history, ai_thinking
    global victory_sparkles, victory_start_ms, _glow_surf_cache
    for r in range(BOARD_SIZE):
        for c in range(BOARD_SIZE):
            board[r][c] = 0
    current_player = 1
    game_over = False
    winner = 0
    move_count = 0
    last_move = None
    win_line = []
    move_history = []
    ai_thinking = False
    victory_sparkles = []
    victory_start_ms = 0
    _glow_surf_cache = None


def set_mode(mode):
    global game_mode, game_state
    if game_mode != mode:
        game_mode = mode
    reset_game()
    if mode == "pve":
        game_state = "color_select"
    else:
        game_state = "playing"


def set_difficulty(level):
    global ai_difficulty
    ai_difficulty = level
    # 切换难度时若对局进行中则重启（仅人机模式）
    if game_mode == "pve" and move_count > 0:
        reset_game()


def _spawn_sparkles():
    """在胜利时生成金色上升粒子"""
    global victory_sparkles, victory_start_ms
    victory_start_ms = pygame.time.get_ticks()
    victory_sparkles = []
    rng = random.Random()
    for _ in range(SPARKLE_COUNT):
        x = rng.uniform(80, WIN_WIDTH - 80)
        y = rng.uniform(20, WIN_HEIGHT * 0.55)
        vx = rng.uniform(-1.2, 1.2)
        vy = rng.uniform(-2.8, -0.6)
        life = rng.uniform(1.0, 2.8)
        victory_sparkles.append([x, y, vx, vy, life, life,
                                 rng.randint(2, 5),
                                 rng.choice(SPARKLE_COLORS)])


# ============================================================
# 绘制函数
# ============================================================
def _get_paper_texture(w, h, seed=42):
    """生成宣纸纹理表面（缓存复用）。"""
    global _paper_cache
    key = (w, h, seed)
    if _paper_cache and _paper_cache[0] == key:
        return _paper_cache[1]
    surf = pygame.Surface((w, h))
    surf.fill(C_PAGE_BG)
    rng = random.Random(seed)
    # 细小纤维点
    for _ in range(w * h // 18):
        x = rng.randint(0, w - 1)
        y = rng.randint(0, h - 1)
        shade = rng.randint(-7, 7)
        clr = (C_PAGE_BG[0] + shade, C_PAGE_BG[1] + shade, C_PAGE_BG[2] + shade)
        surf.set_at((x, y), clr)
    # 稍大纸纹斑点
    for _ in range(w * h // 200):
        x = rng.randint(0, w - 1)
        y = rng.randint(0, h - 1)
        r = rng.randint(1, 4)
        shade = rng.randint(-5, 5)
        clr = (C_PAGE_BG[0] + shade, C_PAGE_BG[1] + shade, C_PAGE_BG[2] + shade)
        pygame.draw.circle(surf, clr, (x, y), r)
    _paper_cache = (key, surf)
    return surf


def draw_background(screen):
    """宣纸纹理背景 + 面板分隔"""
    # 左侧棋盘区 — 宣纸纹理
    paper = _get_paper_texture(PANEL_START_X, WIN_HEIGHT)
    screen.blit(paper, (0, 0))
    # 右侧面板 — 稍深宣纸（用纯色近似）
    panel_tex = pygame.Surface((WIN_WIDTH - PANEL_START_X, WIN_HEIGHT))
    panel_tex.fill(C_PANEL_BG)
    rng = random.Random(99)
    for _ in range((WIN_WIDTH - PANEL_START_X) * WIN_HEIGHT // 25):
        x = rng.randint(0, (WIN_WIDTH - PANEL_START_X) - 1)
        y = rng.randint(0, WIN_HEIGHT - 1)
        shade = rng.randint(-6, 6)
        clr = (C_PANEL_BG[0] + shade, C_PANEL_BG[1] + shade, C_PANEL_BG[2] + shade)
        panel_tex.set_at((x, y), clr)
    screen.blit(panel_tex, (PANEL_START_X, 0))
    # 分隔线 — 淡墨渲染（双线晕染效果）
    x = PANEL_START_X
    sep = pygame.Surface((4, WIN_HEIGHT), pygame.SRCALPHA)
    sep.fill((160, 150, 132, 28))
    screen.blit(sep, (x - 1, 0))
    pygame.draw.line(screen, C_DIVIDER, (x, 0), (x, WIN_HEIGHT), 1)


def draw_board(screen):
    """水墨棋盘 — 淡墨边框 + 宣纸盘面 + 淡墨网格 + 墨点星位 + 行楷坐标"""
    f = FRAME_RECT

    # ① 投影 — 淡墨晕染
    sr = f.copy()
    sr.x += 4; sr.y += 4
    shadow_surf = pygame.Surface(sr.size, pygame.SRCALPHA)
    shadow_surf.fill((25, 20, 15, 38))
    screen.blit(shadow_surf, sr.topleft)

    # ② 浓墨外框
    pygame.draw.rect(screen, C_FRAME_DARK, f, border_radius=6)

    # ③ 中墨内框 — 带水墨渐变感
    inner = pygame.Rect(f.x + FRAME_DEPTH, f.y + FRAME_DEPTH,
                        f.width - FRAME_DEPTH * 2, f.height - FRAME_DEPTH * 2)
    pygame.draw.rect(screen, C_FRAME_LIGHT, inner, border_radius=4)

    # ④ 盘面 — 宣纸色
    face = pygame.Rect(f.x + FRAME_DEPTH * 2, f.y + FRAME_DEPTH * 2,
                       f.width - FRAME_DEPTH * 4, f.height - FRAME_DEPTH * 4)
    pygame.draw.rect(screen, C_BOARD_FACE, face, border_radius=2)

    # 宣纸肌理（盘面加纤维纹理）
    rng = random.Random(77)
    for _ in range(GRID_PIXEL // 2):
        rx = face.x + rng.randint(2, face.width - 2)
        ry = face.y + rng.randint(2, face.height - 2)
        shade = rng.randint(-4, 4)
        clr = (C_BOARD_FACE[0] + shade, C_BOARD_FACE[1] + shade, C_BOARD_FACE[2] + shade)
        screen.set_at((rx, ry), clr)

    # ⑤ 网格线 — 中墨线条，清晰利落，边缘略重
    grid_margin = 5
    gx_start = face.left + grid_margin
    gx_end   = face.right - grid_margin
    gy_start = face.top + grid_margin
    gy_end   = face.bottom - grid_margin

    # 横线
    for i in range(BOARD_SIZE):
        _x, y = board_to_pixel(i, 0)
        edge = (i == 0 or i == BOARD_SIZE - 1)
        lw = 2 if edge else 1
        # 用 alpha 表面画半透明中墨线
        line_surf = pygame.Surface((gx_end - gx_start, 3), pygame.SRCALPHA)
        alpha = 240 if edge else 190
        pygame.draw.line(line_surf, (*C_GRID, alpha), (0, 1), (line_surf.get_width(), 1), lw)
        screen.blit(line_surf, (gx_start, y - 1))

    # 竖线
    for i in range(BOARD_SIZE):
        x, _y = board_to_pixel(0, i)
        edge = (i == 0 or i == BOARD_SIZE - 1)
        lw = 2 if edge else 1
        line_surf = pygame.Surface((3, gy_end - gy_start), pygame.SRCALPHA)
        alpha = 240 if edge else 190
        pygame.draw.line(line_surf, (*C_GRID, alpha), (1, 0), (1, line_surf.get_height()), lw)
        screen.blit(line_surf, (x - 1, gy_start))

    # ⑥ 星位 — 浓墨圆点，带微晕
    for r, c in [(3,3),(3,7),(3,11),(7,3),(7,7),(7,11),(11,3),(11,7),(11,11)]:
        cx, cy = board_to_pixel(r, c)
        # 外晕
        halo = pygame.Surface((10, 10), pygame.SRCALPHA)
        pygame.draw.circle(halo, (*C_STAR, 35), (5, 5), 4)
        screen.blit(halo, (cx - 5, cy - 5))
        # 内点
        pygame.draw.circle(screen, C_STAR, (cx, cy), 3)

    # ⑦ 坐标标注 — 行楷风格
    font = pygame.font.SysFont("simsun", 13, bold=True)
    cols = "ABCDEFGHIJKLMNO"
    for c in range(0, BOARD_SIZE, 2):
        cx, gy_top = board_to_pixel(0, c)
        _, gy_bot  = board_to_pixel(BOARD_SIZE - 1, c)
        t = font.render(cols[c], True, C_LABEL)
        screen.blit(t, t.get_rect(center=(cx, f.top - 12)))
        screen.blit(t, t.get_rect(center=(cx, f.bottom + 12)))
    for r in range(0, BOARD_SIZE, 2):
        gx_left,  cy = board_to_pixel(r, 0)
        gx_right, _  = board_to_pixel(r, BOARD_SIZE - 1)
        t = font.render(str(r + 1), True, C_LABEL)
        screen.blit(t, t.get_rect(center=(f.left - 15, cy)))
        screen.blit(t, t.get_rect(center=(f.right + 15, cy)))


def draw_color_select(screen):
    """先后手选择弹窗 — 水墨卷轴风，居中悬停"""
    if game_state != "color_select":
        return

    # ---- 半透明墨色遮罩 ----
    overlay = pygame.Surface((WIN_WIDTH, WIN_HEIGHT), pygame.SRCALPHA)
    overlay.fill((30, 24, 20, 155))
    screen.blit(overlay, (0, 0))

    # ---- 弹窗尺寸 & 居中 ----
    dlg_w, dlg_h = 400, 270
    dlg_x = (WIN_WIDTH - dlg_w) // 2
    dlg_y = (WIN_HEIGHT - dlg_h) // 2
    dlg = pygame.Rect(dlg_x, dlg_y, dlg_w, dlg_h)
    cx_dlg = dlg_x + dlg_w // 2

    # ---- 宣纸底色 + 浓墨边框 ----
    pygame.draw.rect(screen, C_BOARD_FACE, dlg, border_radius=14)
    pygame.draw.rect(screen, C_FRAME_DARK, dlg, border_radius=14, width=3)

    # ---- 内框淡墨晕染（双层边框层次感） ----
    inner_dlg = pygame.Rect(dlg_x + 6, dlg_y + 6, dlg_w - 12, dlg_h - 12)
    pygame.draw.rect(screen, C_FRAME_LIGHT, inner_dlg, border_radius=10, width=1)

    # ---- 标题 ----
    tfont = pygame.font.SysFont("microsoftyahei", 22, bold=True)
    title = tfont.render("选择先后手", True, C_TITLE)
    screen.blit(title, title.get_rect(center=(cx_dlg, dlg_y + 36)))

    # ---- 副标题 ----
    sfont = pygame.font.SysFont("microsoftyahei", 12)
    sub = sfont.render("执黑先行  ·  执白后行  ·  随机天定", True, C_LABEL)
    screen.blit(sub, sub.get_rect(center=(cx_dlg, dlg_y + 65)))

    # ---- 分隔线 ----
    sep_y = dlg_y + 84
    sep = pygame.Surface((dlg_w - 60, 1), pygame.SRCALPHA)
    sep.fill((195, 188, 172, 130))
    screen.blit(sep, (dlg_x + 30, sep_y))

    # ---- 三选项卡片 ----
    card_w, card_h = 100, 100
    gap = 16
    total_w = card_w * 3 + gap * 2
    card_start_x = dlg_x + (dlg_w - total_w) // 2
    card_y = dlg_y + 100

    mx, my = pygame.mouse.get_pos()

    options = [
        ("color_black",  "执黑", "●", (32, 28, 32),   (248, 245, 238), "先手"),
        ("color_white",  "执白", "○", (232, 226, 216), (52, 44, 36),   "后手"),
        ("color_random", "随机", "?", (110, 100, 88),  (248, 245, 238), "天定"),
    ]

    for i, (bid, label, icon, icon_bg, icon_fg, hint) in enumerate(options):
        cx_card = card_start_x + i * (card_w + gap)
        rect = pygame.Rect(cx_card, card_y, card_w, card_h)
        button_rects.append((rect, bid))

        is_hover = rect.collidepoint(mx, my)

        # 卡片底色
        if is_hover:
            pygame.draw.rect(screen, (225, 218, 204), rect, border_radius=12)
            pygame.draw.rect(screen, C_FRAME_DARK, rect, border_radius=12, width=2)
        else:
            pygame.draw.rect(screen, (242, 237, 228), rect, border_radius=12)
            pygame.draw.rect(screen, C_FRAME_LIGHT, rect, border_radius=12, width=1)

        # 图标底色圆圈
        icon_cy = card_y + 36
        icon_r = 18
        if bid != "color_white":
            pygame.draw.circle(screen, icon_bg, (cx_card + card_w // 2, icon_cy), icon_r)
            if bid == "color_black":
                # 黑子高光
                pygame.draw.circle(screen, (72, 68, 70), (cx_card + card_w // 2 - 3, icon_cy - 3), 6)
        else:
            # 白子多层
            pygame.draw.circle(screen, (192, 186, 176), (cx_card + card_w // 2, icon_cy), icon_r)
            pygame.draw.circle(screen, (236, 231, 222), (cx_card + card_w // 2, icon_cy), icon_r - 2)
            pygame.draw.circle(screen, (248, 245, 240), (cx_card + card_w // 2 - 1, icon_cy - 1), 10)
            # 高光
            pygame.draw.circle(screen, (254, 253, 250), (cx_card + card_w // 2 - 5, icon_cy - 5), 4)

        # 随机图标改为太极符号
        if bid == "color_random":
            # 用半黑半白圆表示随机
            icon_cx = cx_card + card_w // 2
            pygame.draw.circle(screen, icon_bg, (icon_cx, icon_cy), icon_r)
            # 问号文字覆盖
            qfont = pygame.font.SysFont("microsoftyahei", 16, bold=True)
            qtext = qfont.render("?", True, (248, 245, 238))
            screen.blit(qtext, qtext.get_rect(center=(icon_cx, icon_cy)))

        # 标签文字
        lfont = pygame.font.SysFont("microsoftyahei", 13, bold=True)
        ltext = lfont.render(label, True, C_TITLE if not is_hover else C_FRAME_DARK)
        screen.blit(ltext, ltext.get_rect(center=(cx_card + card_w // 2, card_y + 72)))

        # 副提示
        hfont = pygame.font.SysFont("microsoftyahei", 10)
        htext = hfont.render(hint, True, C_LABEL)
        screen.blit(htext, htext.get_rect(center=(cx_card + card_w // 2, card_y + 90)))

    # ---- 底部提示 ----
    tip = pygame.font.SysFont("microsoftyahei", 11).render("点击选择后开始对局", True, C_LABEL)
    screen.blit(tip, tip.get_rect(center=(cx_dlg, dlg_y + dlg_h - 18)))


def draw_turn_indicator(screen):
    """棋盘正上方 — 印章式回合徽章"""
    cx = BOARD_AREA_WIDTH // 2
    chip_y = max(14, OFFSET_Y - FRAME_MARGIN - 22)

    if game_state == "color_select":
        label, bg = "请选择先后手", (105, 90, 72)
    elif game_over:
        if winner == 0:
            label, bg = "握手言和", TURN_DRAW
        elif winner == 1:
            label, bg = "黑棋胜", TURN_WIN_B
        else:
            label, bg = "白棋胜", TURN_WIN_W
    else:
        if game_mode == "pve" and current_player == 2:
            diff_map = {"easy": "简单", "medium": "中等", "hard": "困难"}
            label, bg = f"AI（{diff_map.get(ai_difficulty, '中等')}）", TURN_AI
        elif current_player == 1:
            label, bg = "黑棋落子", TURN_BLACK
        else:
            label, bg = "白棋落子", TURN_WHITE

    font = pygame.font.SysFont("microsoftyahei", 15, bold=True)
    text = font.render(label, True, TURN_TEXT_C)
    pw, ph = text.get_width() + 24, 26
    chip_rect = pygame.Rect(cx - pw // 2, chip_y - ph // 2, pw, ph)

    # 淡墨阴影
    sr = chip_rect.copy(); sr.y += 2
    pygame.draw.rect(screen, (55, 48, 38, 30), sr, border_radius=10)
    pygame.draw.rect(screen, bg, chip_rect, border_radius=10)
    # 微高光边
    hl = pygame.Surface((pw, ph), pygame.SRCALPHA)
    pygame.draw.rect(hl, (255, 255, 255, 25), pygame.Rect(0, 0, pw, ph), border_radius=10, width=1)
    screen.blit(hl, chip_rect.topleft)
    screen.blit(text, text.get_rect(center=chip_rect.center))


def draw_mode_buttons(screen):
    """棋盘右上角 — 双人对战 / 人机对战 切换（印章式）"""
    btn_w, btn_h, gap = 70, 24, 8
    start_x = BOARD_AREA_WIDTH - 18 - btn_w * 2 - gap
    start_y = 10
    font = pygame.font.SysFont("microsoftyahei", 12, bold=True)

    for i, (mid, mlabel) in enumerate([("pvp", "双人对弈"), ("pve", "人机对弈")]):
        bx = start_x + i * (btn_w + gap)
        rect = pygame.Rect(bx, start_y, btn_w, btn_h)
        button_rects.append((rect, f"mode_{mid}"))

        is_active = (game_mode == mid)
        mx, my = pygame.mouse.get_pos()
        is_hover = rect.collidepoint(mx, my) and not is_active

        if is_active:
            bg = MODE_PVP_ACTIVE if mid == "pvp" else MODE_PVE_ACTIVE
            tc = (248, 245, 238)
        elif is_hover:
            bg = (95, 86, 76)
            tc = (248, 245, 238)
        else:
            bg = MODE_PVP_NORMAL if mid == "pvp" else MODE_PVE_NORMAL
            tc = (72, 64, 55)

        # 按钮阴影
        shadow_rect = rect.copy(); shadow_rect.y += 1
        pygame.draw.rect(screen, (165, 155, 140, 35), shadow_rect, border_radius=6)
        pygame.draw.rect(screen, bg, rect, border_radius=6)
        if is_active:
            hl = pygame.Surface((btn_w, btn_h), pygame.SRCALPHA)
            pygame.draw.rect(hl, (255, 255, 255, 30), pygame.Rect(0, 0, btn_w, btn_h), border_radius=6, width=1)
            screen.blit(hl, rect.topleft)

        text = font.render(mlabel, True, tc)
        screen.blit(text, text.get_rect(center=rect.center))


def draw_stones(screen):
    """绘制所有棋子 — 3D 渐变 + 阴影 + 胜利光晕 + 最后落子标记"""
    global _glow_surf_cache
    win_set = set(win_line) if game_over and win_line else set()

    # 预生成光晕表面（仅当有胜利棋子且缓存未命中时）
    gc = STONE_RADIUS + 5
    has_win = bool(win_set)
    if has_win and _glow_surf_cache is None:
        _glow_surf_cache = pygame.Surface((STONE_RADIUS * 2 + 10, STONE_RADIUS * 2 + 10), pygame.SRCALPHA)
        for ring in range(5, 0, -1):
            alpha = 25 * ring
            pygame.draw.circle(_glow_surf_cache, (218, 175, 60, alpha), (gc, gc), STONE_RADIUS + ring)

    for r in range(BOARD_SIZE):
        for c in range(BOARD_SIZE):
            v = board[r][c]
            if v == 0:
                continue
            cx, cy = board_to_pixel(r, c)
            is_black = (v == 1)
            is_win = ((r, c) in win_set)

            # 胜利棋子外圈金色光晕（复用预生成表面）
            if is_win and _glow_surf_cache is not None:
                screen.blit(_glow_surf_cache, (cx - gc, cy - gc))

            # 阴影
            pygame.draw.circle(screen, SHADOW_COLOR,
                               (cx + SHADOW_DX, cy + SHADOW_DY), STONE_RADIUS)
            # 3D 渐变棋子
            _draw_3d_stone(screen, cx, cy, is_black)

            # 最后落子标记
            if (r, c) == last_move:
                if game_over and winner != 0:
                    pygame.draw.circle(screen, (198, 55, 48), (cx, cy), 4)  # 朱砂红
                elif not game_over:
                    pygame.draw.circle(screen, (52, 45, 38), (cx, cy), 4)   # 浓墨点


def _draw_3d_stone(screen, cx, cy, is_black):
    """
    水墨风棋子：
      黑子 — 浓墨效果，深沉内敛，含微光晕
      白子 — 暖玉石感，温润柔和
    """
    r = STONE_RADIUS
    if is_black:
        # 墨色黑子：深墨底 → 浓墨体 → 中墨过渡 → 微高光
        c_edge = (16, 15, 18)
        c_body = (28, 26, 30)
        c_inner = (48, 44, 47)
        c_highlight = (78, 74, 72)
    else:
        # 玉石白子：暖灰边 → 米白体 → 近白内层 → 柔和高光
        c_edge = (192, 186, 176)
        c_body = (236, 231, 222)
        c_inner = (248, 245, 240)
        c_highlight = (254, 253, 250)

    # Layer 1: 底圆（边缘色）
    pygame.draw.circle(screen, c_edge, (cx, cy), r)
    # Layer 2: 主体（稍小）
    pygame.draw.circle(screen, c_body, (cx, cy), r - 1)
    # Layer 3: 内层亮区（偏左上）
    offset = 1
    pygame.draw.circle(screen, c_inner, (cx - offset, cy - offset), int(r * 0.72))
    # Layer 4: 高光（左上柔光）
    hl_r = r // 3
    pygame.draw.circle(screen, c_highlight, (cx - r // 2 + 1, cy - r // 2 + 1), max(hl_r, 2))


def draw_hover_preview(screen):
    """鼠标悬停 — 半透明墨色预览棋子"""
    global hover_pos
    mx, my = pygame.mouse.get_pos()
    result = pixel_to_board(mx, my)
    if result is None:
        hover_pos = None
        return
    r, c = result
    hover_pos = (r, c)
    if board[r][c] != 0 or game_over:
        return
    if game_mode == "pve" and current_player != player_color:
        return

    cx, cy = board_to_pixel(r, c)
    if current_player == 1:
        alpha = 80
        clr = (28, 24, 28, alpha)
    else:
        alpha = 130
        clr = (155, 145, 130, alpha)
    s = pygame.Surface((STONE_RADIUS * 2, STONE_RADIUS * 2), pygame.SRCALPHA)
    pygame.draw.circle(s, clr, (STONE_RADIUS, STONE_RADIUS), STONE_RADIUS)
    screen.blit(s, (cx - STONE_RADIUS, cy - STONE_RADIUS))


def draw_panel(screen):
    """右侧面板 — 水墨卷轴风"""
    px = PANEL_START_X
    pw = WIN_WIDTH - PANEL_START_X
    cx_panel = px + pw // 2
    M = px + 20

    # ===== ① 标题 — 行楷大字 =====
    font_title = pygame.font.SysFont("microsoftyahei", 28, bold=True)
    t = font_title.render("五子棋", True, C_TITLE)
    screen.blit(t, t.get_rect(center=(cx_panel, 38)))
    # 淡墨分隔
    sep = pygame.Surface((pw - 28, 1), pygame.SRCALPHA)
    sep.fill((195, 188, 172, 120))
    screen.blit(sep, (px + 14, 62))

    # ===== ② 模式 =====
    mode_label = "人机对弈" if game_mode == "pve" else "双人对弈"
    mode_clr = (98, 82, 66) if game_mode == "pve" else (78, 68, 52)
    fm = pygame.font.SysFont("microsoftyahei", 13, bold=True)
    screen.blit(fm.render(f"棋局：{mode_label}", True, mode_clr), (M, 72))

    # ===== ②.5 人机难度选择（仅 PVE 模式显示）=====
    diff_pushed = 0
    if game_mode == "pve":
        _draw_difficulty_buttons(screen)
        diff_pushed = 30

    # ===== ③ 胜场统计 =====
    score_y = 96 + diff_pushed
    fs = pygame.font.SysFont("microsoftyahei", 24, bold=True)
    fl = pygame.font.SysFont("microsoftyahei", 11)

    cols_data = [
        ("●", black_wins, (52, 44, 36)),
        ("—", draws,      (148, 138, 122)),
        ("○", white_wins, (98, 88, 74)),
    ]
    col_w = (pw - 20) // 3
    for i, (icon, val, iclr) in enumerate(cols_data):
        col_x = px + 10 + i * col_w
        ic = fs.render(icon, True, iclr)
        screen.blit(ic, ic.get_rect(center=(col_x + col_w // 2, score_y)))
        vt = fl.render(str(val), True, C_VALUE)
        screen.blit(vt, vt.get_rect(center=(col_x + col_w // 2, score_y + 22)))

    # ===== ④ 对局统计 =====
    stats_y = 144
    sep2 = pygame.Surface((pw - 28, 1), pygame.SRCALPHA)
    sep2.fill((195, 188, 172, 120))
    screen.blit(sep2, (px + 14, stats_y))

    flab = pygame.font.SysFont("microsoftyahei", 12)
    fval = pygame.font.SysFont("microsoftyahei", 13, bold=True)

    y = stats_y + 14
    screen.blit(flab.render("手数", True, C_SEC_TITLE), (M, y))
    v = fval.render(str(move_count), True, C_VALUE)
    screen.blit(v, (px + pw - v.get_width() - 20, y))

    y += 26
    screen.blit(flab.render("落子", True, C_SEC_TITLE), (M, y))
    if last_move:
        col_letters = "ABCDEFGHIJKLMNO"
        r, c = last_move
        stone_sym = "●" if board[r][c] == 1 else "○"
        lv = fval.render(f"{stone_sym} {col_letters[c]}{r + 1}", True, C_VALUE)
        screen.blit(lv, (px + pw - lv.get_width() - 20, y))

    # ===== ⑤ 提示 =====
    tips_y = y + 38
    sep3 = pygame.Surface((pw - 28, 1), pygame.SRCALPHA)
    sep3.fill((195, 188, 172, 120))
    screen.blit(sep3, (px + 14, tips_y - 4))

    ft1 = pygame.font.SysFont("microsoftyahei", 12, bold=True)
    ft2 = pygame.font.SysFont("microsoftyahei", 11)
    screen.blit(ft1.render("棋谱", True, C_TIP_LABEL), (M, tips_y))
    tips_y += 20
    screen.blit(ft2.render("左键落子 · R键新局", True, C_TIP_TEXT), (M, tips_y))

    # ===== ⑥ 功能按钮 =====
    _draw_buttons(screen, tips_y + 18)


def _draw_buttons(screen, start_y):
    """面板底部功能按钮 — 水墨印章式"""
    mx, my = pygame.mouse.get_pos()
    px = PANEL_START_X
    pw = WIN_WIDTH - PANEL_START_X
    btn_w = pw - 32
    btn_h = 34
    btn_x = px + 16
    gap = 10

    buttons = [
        ("restart", "新局",  BTN_DARK,   BTN_DARK_H,   BTN_TEXT_C),
        ("undo",    "悔棋", BTN_MID,    BTN_MID_H,    BTN_TEXT_C),
        ("quit",    "收子", BTN_ACCENT, BTN_ACCENT_H, BTN_TEXT_C),
    ]

    for i, (bid, label, bc, bch, tc) in enumerate(buttons):
        by = start_y + i * (btn_h + gap)
        rect = pygame.Rect(btn_x, by, btn_w, btn_h)
        button_rects.append((rect, bid))

        is_hover = rect.collidepoint(mx, my)
        bg = bch if is_hover else bc

        if is_hover:
            sr = rect.copy(); sr.y += 2
            pygame.draw.rect(screen, (95, 82, 65, 30), sr, border_radius=8)

        pygame.draw.rect(screen, bg, rect, border_radius=8)
        if is_hover:
            hl = pygame.Surface((btn_w, btn_h), pygame.SRCALPHA)
            pygame.draw.rect(hl, (255, 255, 255, 25), pygame.Rect(0, 0, btn_w, btn_h), border_radius=8, width=2)
            screen.blit(hl, rect.topleft)

        font = pygame.font.SysFont("microsoftyahei", 14, bold=True)
        text = font.render(label, True, tc)
        screen.blit(text, text.get_rect(center=rect.center))


def _draw_difficulty_buttons(screen):
    """面板中的人机难度选择按钮（易 / 中 / 难）"""
    mx, my = pygame.mouse.get_pos()
    px = PANEL_START_X
    pw = WIN_WIDTH - PANEL_START_X
    btn_h = 22
    gap = 6
    btn_w = (pw - 32 - gap * 2) // 3
    base_x = px + 16
    base_y = 94

    diffs = [
        ("easy",   "易", DIFF_EASY_ACTIVE,   DIFF_EASY_NORMAL),
        ("medium", "中", DIFF_MEDIUM_ACTIVE, DIFF_MEDIUM_NORMAL),
        ("hard",   "难", DIFF_HARD_ACTIVE,   DIFF_HARD_NORMAL),
    ]

    font = pygame.font.SysFont("microsoftyahei", 11, bold=True)
    for i, (did, dlabel, active_c, normal_c) in enumerate(diffs):
        bx = base_x + i * (btn_w + gap)
        rect = pygame.Rect(bx, base_y, btn_w, btn_h)
        button_rects.append((rect, f"diff_{did}"))

        is_active = (ai_difficulty == did)
        is_hover = rect.collidepoint(mx, my) and not is_active

        if is_active:
            bg, tc = active_c, (248, 245, 238)
        elif is_hover:
            bg, tc = active_c, (248, 245, 238)
            bg = tuple(min(c + 25, 255) for c in bg)
        else:
            bg, tc = normal_c, (105, 92, 72)

        pygame.draw.rect(screen, bg, rect, border_radius=5)
        if is_active:
            hl = pygame.Surface((btn_w, btn_h), pygame.SRCALPHA)
            pygame.draw.rect(hl, (255, 255, 255, 40), pygame.Rect(0, 0, btn_w, btn_h), border_radius=5, width=1)
            screen.blit(hl, rect.topleft)

        text = font.render(dlabel, True, tc)
        screen.blit(text, text.get_rect(center=rect.center))


def draw_victory_banner(screen):
    """胜利横幅 — 淡墨晕染 + 朱砂印色文字"""
    if not game_over or winner == 0:
        return

    elapsed = pygame.time.get_ticks() - victory_start_ms
    pulse = 0.5 + 0.5 * math.sin(elapsed * 0.004)

    banner_h = 55
    banner = pygame.Surface((WIN_WIDTH, banner_h), pygame.SRCALPHA)
    # 淡墨渐晕
    for i in range(banner_h):
        alpha = 185 - i * 3
        r = 35
        g = 28
        b = 22
        pygame.draw.line(banner, (r, g, b, max(alpha, 60)),
                         (0, i), (WIN_WIDTH, i))
    screen.blit(banner, (0, 0))

    # 装饰线 — 淡金 + 朱砂双线
    gold_alpha = int(160 + 50 * pulse)
    top_line = pygame.Surface((WIN_WIDTH - 80, 2), pygame.SRCALPHA)
    pygame.draw.line(top_line, (195, 162, 78, gold_alpha), (0, 1), (top_line.get_width(), 1), 1)
    screen.blit(top_line, (40, 2))
    bot_line = pygame.Surface((WIN_WIDTH - 80, 3), pygame.SRCALPHA)
    pygame.draw.line(bot_line, (178, 45, 38, gold_alpha), (0, 1), (bot_line.get_width(), 1), 2)
    screen.blit(bot_line, (40, banner_h - 2))

    # 文字 — 朱砂印色
    is_black = (winner == 1)
    label = "黑棋胜" if is_black else "白棋胜"

    scale = 1.0 + 0.03 * pulse
    font_size = int(32 * scale)
    main_font = pygame.font.SysFont("microsoftyahei", font_size, bold=True)
    tc_r = 212 - int(55 * pulse)
    tc_g = 148 - int(40 * pulse)
    tc_b = 105 - int(35 * pulse)
    main_text = main_font.render(label, True,
                                 (max(tc_r, 165), max(tc_g, 105), max(tc_b, 72)))
    main_rect = main_text.get_rect(center=(WIN_WIDTH // 2, banner_h // 2))

    # 淡墨辉光
    glow_font = pygame.font.SysFont("microsoftyahei", font_size, bold=True)
    glow = glow_font.render(label, True, (195, 85, 50))
    glow.set_alpha(50 + int(30 * pulse))
    for dx, dy in [(-1,-1),(1,-1),(-1,1),(1,1)]:
        screen.blit(glow, main_rect.move(dx, dy))

    screen.blit(main_text, main_rect)


def draw_victory_overlay(screen):
    """棋盘区极淡墨色遮罩"""
    if not game_over:
        return
    overlay = pygame.Surface((BOARD_AREA_WIDTH, WIN_HEIGHT), pygame.SRCALPHA)
    overlay.fill((238, 234, 225, 15))
    screen.blit(overlay, (0, 0))


def draw_sparkles(screen):
    """胜利粒子动画 — 墨色金点上升"""
    if not victory_sparkles:
        return

    dt = 1.0 / FPS
    for s in victory_sparkles[:]:
        s[0] += s[2]
        s[1] += s[3]
        s[4] -= dt
        if s[4] <= 0:
            victory_sparkles.remove(s)
            continue

        alpha_fade = s[4] / s[5]
        size = s[6]
        color = s[7]
        alpha = int(200 * alpha_fade)

        spark_surf = pygame.Surface((size * 2 + 4, size * 2 + 4), pygame.SRCALPHA)
        # 外光晕 — 淡金色
        pygame.draw.circle(spark_surf, (*color, alpha // 3),
                           (size + 2, size + 2), size + 1)
        # 内亮点
        pygame.draw.circle(spark_surf, (*color, alpha),
                           (size + 2, size + 2), size)
        screen.blit(spark_surf, (int(s[0]) - size - 2, int(s[1]) - size - 2))


# ============================================================
# 胜负检测
# ============================================================
DIRECTIONS = [(0, 1), (1, 0), (1, 1), (1, -1)]


def _count_in_direction(row, col, dr, dc, player):
    """沿 (dr,dc) 正方向计数连续同色棋子，返回连续个数。"""
    cnt = 0
    for step in range(1, 5):
        nr, nc = row + dr * step, col + dc * step
        if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and board[nr][nc] == player:
            cnt += 1
        else:
            break
    return cnt


def _collect_cells(row, col, dr, dc, player):
    """沿 (dr,dc) 正反方向收集连续同色棋子坐标列表。"""
    cells = [(row, col)]
    for sign in (1, -1):
        for step in range(1, 5):
            nr, nc = row + dr * sign * step, col + dc * sign * step
            if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and board[nr][nc] == player:
                cells.append((nr, nc))
            else:
                break
    return cells


def check_win(row, col):
    player = board[row][col]
    if player == 0:
        return False, []

    for dr, dc in DIRECTIONS:
        # 快速剪枝：该方向最大可能长度
        pos_cnt = _count_in_direction(row, col, dr, dc, player)
        neg_cnt = _count_in_direction(row, col, -dr, -dc, player)
        if pos_cnt + neg_cnt + 1 < 5:
            continue

        cells = _collect_cells(row, col, dr, dc, player)
        if len(cells) >= 5:
            return True, cells
    return False, []


# ============================================================
# 游戏逻辑
# ============================================================
def place_stone(row, col):
    global current_player, game_over, winner, move_count, last_move, win_line
    global black_wins, white_wins, draws

    if board[row][col] != 0 or game_over:
        return False

    board[row][col] = current_player
    move_history.append((row, col, current_player))
    move_count += 1
    last_move = (row, col)

    has_win, line = check_win(row, col)
    if has_win:
        game_over = True
        winner = current_player
        win_line = line
        if winner == 1:
            black_wins += 1
        else:
            white_wins += 1
        _spawn_sparkles()
        return True

    if move_count >= BOARD_SIZE * BOARD_SIZE:
        game_over = True
        winner = 0
        draws += 1
        _spawn_sparkles()
        return True

    current_player = 3 - current_player
    return True


def undo_move():
    global current_player, game_over, winner, move_count, last_move, win_line
    if not move_history:
        return False

    row, col, player = move_history.pop()
    board[row][col] = 0
    move_count -= 1
    current_player = player

    last_move = move_history[-1][:2] if move_history else None
    game_over = False
    winner = 0
    win_line = []
    return True


# ============================================================
# AI 智能落子 — 三级难度
# ============================================================
CENTER = BOARD_SIZE // 2

_PATTERN_SCORE = {
    (5, 2): 100000, (5, 1): 100000,
    (4, 2): 10000,
    (4, 1): 2000,
    (3, 2): 1000,
    (3, 1): 200,
    (2, 2): 100,
    (2, 1): 20,
    (1, 2): 10,
    (1, 1): 2,
}


def _eval_cell(r, c, player):
    """评估某空位对指定玩家的价值（连子长度 + 开放端）。"""
    if board[r][c] != 0:
        return 0
    total = 0
    for dr, dc in DIRECTIONS:
        pos_cnt = _count_in_direction(r, c, dr, dc, player)
        neg_cnt = _count_in_direction(r, c, -dr, -dc, player)
        count = pos_cnt + neg_cnt + 1
        open_ends = 0
        pr, pc = r + dr * (pos_cnt + 1), c + dc * (pos_cnt + 1)
        if 0 <= pr < BOARD_SIZE and 0 <= pc < BOARD_SIZE and board[pr][pc] == 0:
            open_ends += 1
        nr2, nc2 = r - dr * (neg_cnt + 1), c - dc * (neg_cnt + 1)
        if 0 <= nr2 < BOARD_SIZE and 0 <= nc2 < BOARD_SIZE and board[nr2][nc2] == 0:
            open_ends += 1
        key = (min(count, 5), min(open_ends, 2))
        total += _PATTERN_SCORE.get(key, 0)
    return total


def _center_bonus(r, c):
    """距离中心越近，加分越高（引导 AI 占据中央）。"""
    dist = ((r - CENTER) ** 2 + (c - CENTER) ** 2) ** 0.5
    return max(0, int((BOARD_SIZE - dist) * 0.6))


# ── 简单级：随机落子 ──────────────────────────────────────────
def _ai_easy():
    """随机选择一个空位落子，降低入门门槛。"""
    empty = [(r, c) for r in range(BOARD_SIZE) for c in range(BOARD_SIZE)
             if board[r][c] == 0]
    if empty:
        r, c = random.choice(empty)
        place_stone(r, c)
    return bool(empty)


# ── 中等级：防守为主 ──────────────────────────────────────────
def _ai_medium():
    """优先拦截玩家的连子威胁，仅在明显机会下进攻。"""
    best_score = -1
    best_cells = []
    cand_count = 0

    for r in range(BOARD_SIZE):
        for c in range(BOARD_SIZE):
            if board[r][c] != 0:
                continue
            defense = _eval_cell(r, c, 1)    # 拦截玩家
            attack  = _eval_cell(r, c, 2)    # AI 自身进攻
            score   = int(defense * 1.8 + attack * 0.6) + _center_bonus(r, c)

            # 若防守分值已很高（玩家快赢了），单独提升权重
            if defense >= 10000:
                score += 50000

            if score > best_score:
                best_score = score
                best_cells = [(r, c)]
            elif score == best_score:
                best_cells.append((r, c))
            cand_count += 1

    if cand_count == 0:
        return False

    r, c = random.choice(best_cells)
    place_stone(r, c)
    return True


# ── 困难级：攻守兼备，多条件优化 ──────────────────────────────
def _ai_hard():
    """
    1. 检测自身必胜点（连 5），立即落子。
    2. 检测对手必胜点，优先封堵。
    3. 综合评估攻防分值 + 中心偏好 + 邻近度。
    """
    # 第一遍：检查必胜 / 必堵
    winning_moves = []
    must_block = []

    for r in range(BOARD_SIZE):
        for c in range(BOARD_SIZE):
            if board[r][c] != 0:
                continue
            # AI 若此步能连五 → 直接赢
            board[r][c] = 2
            has_win, _ = check_win(r, c)
            board[r][c] = 0
            if has_win:
                winning_moves.append((r, c))
            # 对手若此步能连五 → 必须堵
            board[r][c] = 1
            opp_win, _ = check_win(r, c)
            board[r][c] = 0
            if opp_win:
                must_block.append((r, c))

    if winning_moves:
        place_stone(*winning_moves[0])
        return True
    if must_block:
        # 有多个必堵点时选中心最近的
        best = min(must_block, key=lambda p: abs(p[0] - CENTER) + abs(p[1] - CENTER))
        place_stone(*best)
        return True

    # 第二遍：常规评估 + 邻近度加权
    best_score = -1
    best_cells = []

    for r in range(BOARD_SIZE):
        for c in range(BOARD_SIZE):
            if board[r][c] != 0:
                continue

            attack  = _eval_cell(r, c, 2)
            defense = _eval_cell(r, c, 1)

            # 邻近度加分（附近有棋子时更有价值）
            neighbor_bonus = 0
            for dr2 in (-1, 0, 1):
                for dc2 in (-1, 0, 1):
                    if dr2 == 0 and dc2 == 0:
                        continue
                    nr, nc = r + dr2, c + dc2
                    if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and board[nr][nc] != 0:
                        neighbor_bonus += 5

            score = attack + int(defense * 1.15) + _center_bonus(r, c) + neighbor_bonus

            if score > best_score:
                best_score = score
                best_cells = [(r, c)]
            elif score == best_score:
                best_cells.append((r, c))

    if not best_cells:
        return False

    r, c = random.choice(best_cells)
    place_stone(r, c)
    return True


# ── 调度入口 ──────────────────────────────────────────────────
def ai_move():
    global ai_thinking
    ok = False
    if ai_difficulty == "easy":
        ok = _ai_easy()
    elif ai_difficulty == "hard":
        ok = _ai_hard()
    else:
        ok = _ai_medium()
    ai_thinking = False
    return ok


# ============================================================
# 主循环
# ============================================================
def main():
    global ai_thinking, ai_think_start, game_state, player_color

    pygame.init()
    screen = pygame.display.set_mode((WIN_WIDTH, WIN_HEIGHT))
    pygame.display.set_caption("五子棋")
    clock = pygame.time.Clock()

    running = True
    while running:
        # ----- 事件处理 -----
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False

            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                btn_clicked = False
                for rect, bid in button_rects:
                    if rect.collidepoint(event.pos):
                        btn_clicked = True
                        if bid == "restart":
                            reset_game()
                            if game_mode == "pve":
                                game_state = "color_select"
                        elif bid == "undo":
                            if game_mode == "pve" and len(move_history) >= 2:
                                undo_move()
                                undo_move()
                            else:
                                undo_move()
                        elif bid == "quit":
                            running = False
                        elif bid == "mode_pvp":
                            set_mode("pvp")
                        elif bid == "mode_pve":
                            set_mode("pve")
                        elif bid == "diff_easy":
                            set_difficulty("easy")
                        elif bid == "diff_medium":
                            set_difficulty("medium")
                        elif bid == "diff_hard":
                            set_difficulty("hard")
                        # ---- 先后手选择 ----
                        elif bid == "color_black":
                            player_color = 1
                            game_state = "playing"
                            reset_game()
                        elif bid == "color_white":
                            player_color = 2
                            game_state = "playing"
                            reset_game()
                            ai_thinking = True
                            ai_think_start = pygame.time.get_ticks()
                        elif bid == "color_random":
                            player_color = random.choice([1, 2])
                            game_state = "playing"
                            reset_game()
                            if player_color == 2:
                                ai_thinking = True
                                ai_think_start = pygame.time.get_ticks()
                        break
                if not btn_clicked:
                    can_play = (game_mode == "pvp" or
                                (game_mode == "pve" and current_player == player_color))
                    if can_play:
                        result = pixel_to_board(*event.pos)
                        if result is not None:
                            placed = place_stone(*result)
                            if placed and game_mode == "pve" and not game_over:
                                ai_thinking = True
                                ai_think_start = pygame.time.get_ticks()

            if event.type == pygame.KEYDOWN and event.key == pygame.K_r:
                reset_game()
                if game_mode == "pve":
                    game_state = "color_select"

        # ----- AI 延时落子 -----
        if ai_thinking and not game_over:
            if pygame.time.get_ticks() - ai_think_start >= 400:
                ai_move()

        # ----- 每帧重建点击区域 -----
        button_rects.clear()

        # ----- 绘制 -----
        draw_background(screen)
        draw_board(screen)
        draw_turn_indicator(screen)
        draw_mode_buttons(screen)
        if game_state == "playing":
            draw_stones(screen)
            draw_hover_preview(screen)
            draw_victory_overlay(screen)
            draw_sparkles(screen)
            draw_victory_banner(screen)
        draw_panel(screen)
        draw_color_select(screen)        # 最后绘制，覆盖在所有元素之上

        pygame.display.flip()
        clock.tick(FPS)

    pygame.quit()
    sys.exit()


if __name__ == "__main__":
    main()
