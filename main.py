import uasyncio as asyncio
import urequests as requests
import ujson as json
import network, machine, ntptime, time, math, gc
from machine import Pin, SPI
import ili9341
from xglcd_font import XglcdFont

# ───────────────────────────────────────────────
MODE_TEST = False
# ───────────────────────────────────────────────

global_state = {
    'config':         {},
    'wifi_connected': asyncio.Event(),
    'time_updated':   asyncio.Event(),
    'meteo_ready':    asyncio.Event(),   # déclenché après 1er relevé (TZ connu)
    'meteo_data':     {},
    'local_time':     None,
    'tz_offset':      0,
    'tz_name':        'UTC',
    'error':          None,
}

DEFAULT_CONFIG = {
    "target": "wokwi-esp32",
    "langue": "Fr-FR",
    "location": {"ville": "", "pays": "", "latitude": 0, "longitude": 0},
    "wifi":     {"ssid": "", "password": ""},
    "heartbeat_led": {"pin": 21, "neopixel": False},
    "tft": {
        "width": 320, "height": 240, "rotation": 270,
        "spi":  {"sck": 18, "mosi": 23, "miso": 19},
        "pins": {"cs": 5,  "dc": 2,   "rst": 4}
    },
    "meteo_freq": 600
}

# ── Palette RGB565 ───────────────────────────────────────────────────────────
C_BLACK  = ili9341.color565(  0,   0,   0)
C_WHITE  = ili9341.color565(255, 255, 255)
C_RED    = ili9341.color565(220,  55,  55)
C_GREEN  = ili9341.color565( 55, 210,  80)
C_BLUE   = ili9341.color565( 30, 144, 255)
C_CYAN   = ili9341.color565(  0, 210, 210)
C_YELLOW = ili9341.color565(255, 215,   0)
C_ORANGE = ili9341.color565(255, 145,   0)
C_GRAY   = ili9341.color565( 90,  90,  90)
C_LTGRAY = ili9341.color565(160, 160, 160)
C_DKBLUE = ili9341.color565(  0,  18,  70)
C_DKGRAY = ili9341.color565( 26,  26,  36)
C_NAVY   = ili9341.color565(  0,   8,  48)

# ── Layout 320×240 ───────────────────────────────────────────────────────────
#
#   Ligne 1  y=  0.. 27   Ville (centré)          DKBLUE
#   Ligne 2  y= 28.. 55   Date + Heure (centré)   DKGRAY   ← mis à jour /s
#   Ligne 3  y= 56.. 83   (TZ - UTC+X) (centré)   DKGRAY
#   Ligne 4  y= 84..111   Météo (centré)           BLACK
#   Zone GFX y=112..239   Horloge │ Lune           BLACK
#
TY0, TY1 =   0,  27   # titre
DY0, DY1 =  28,  55   # date + heure
ZY0, ZY1 =  56,  83   # fuseau
MY0, MY1 =  84, 111   # météo
GX0, GX1 = 112, 239   # graphiques

ROW_H = 28   # hauteur d'une ligne texte (police 24px + 4px marge)

# ── Horloge analogique (double-buffer) ──────────────────────────────────────
# Le buffer couvre exactement le disque de l'horloge + marge de 2px.
CLK_R  = 40           # rayon (px)  — R=55 = 26 KB > heap ESP32 ; R=40 = 14 KB OK
CLK_CX = 80           # centre X écran
CLK_CY = 176          # centre Y écran  (GX0 + 64)
# Le buffer est un carré centré sur l'horloge, côté = 2×(CLK_R+2)
_CS    = (CLK_R + 2) * 2          # côté du carré = 84px → 84×84×2 = 14112 octets
CLK_BX = CLK_CX - CLK_R - 2      # x écran coin haut-gauche = 38
CLK_BY = CLK_CY - CLK_R - 2      # y écran coin haut-gauche = 134  (>GX0=112 ✓)
CLK_CX_BUF = CLK_R + 2           # centre X dans le buffer = 42
CLK_CY_BUF = CLK_R + 2           # centre Y dans le buffer = 42


# Séparateur horloge/lune
VSEP_X = 163          # x ligne verticale

# ── Lune (direct, mise à jour /60s) ─────────────────────────────────────────
MOON_CX  = 240        # centre X écran
MOON_CY  = 168        # centre Y écran  (GX0 + 56)
MOON_R   = 38         # rayon (px)
MOON_TY  = 210        # y texte nom de phase


# ────────────────────────────────────────────────────────────────────────────
# DESSIN HORLOGE ANALOGIQUE (dessin direct sur display)
# ────────────────────────────────────────────────────────────────────────────
# ── Mois français ────────────────────────────────────────────────────────────
_MOIS = ["","JANVIER","FEVRIER","MARS","AVRIL","MAI","JUIN",
         "JUILLET","AOUT","SEPTEMBRE","OCTOBRE","NOVEMBRE","DECEMBRE"]

# ── Phase lunaire ────────────────────────────────────────────────────────────
_NM_REF  = 947182440        # Nouvelle lune ref. 2000-01-06 18:14 UTC
_SYNODIC = 2551442          # 29.530588 jours en secondes
_MOON_NAMES = [
    "Nvlle lune","Crois.croi","1er quart.","Gibb.croi.",
    "Plne lune ","Gibb.decr.","Der.quart.","Crois.decr"
]

def moon_phase():
    """Retourne (fraction [0-1], nom) de la phase lunaire courante."""
    p = ((time.time() - _NM_REF) % _SYNODIC) / _SYNODIC
    return p, _MOON_NAMES[min(7, int(p * 8))]

# ── Utilitaires généraux ─────────────────────────────────────────────────────
def url_encode(s):
    safe = ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
            "0123456789-_.~")
    out = ""
    for c in s:
        out += c if c in safe else ("%" + "%02X" % ord(c))
    return out

def get_local_time():
    """Heure locale = UTC (RTC) + offset fourni par Open-Meteo (DST inclus)."""
    return time.localtime(time.time() + global_state['tz_offset'])

def wind_label(deg):
    if deg is None: return "---"
    dirs = ["N","NNE","NE","ENE","E","ESE","SE","SSE",
            "S","SSO","SO","OSO","O","ONO","NO","NNO"]
    return dirs[int((float(deg) + 11.25) / 22.5) % 16]

def sep(c="-", n=44):
    print(c * n)


def _hand(buf, cx, cy, angle_deg, length, color, thick=1):
    """Dessine une aiguille épaisse (thick lignes parallèles)."""
    a  = math.radians(angle_deg - 90)
    ca = math.cos(a); sa = math.sin(a)
    ex = cx + int(length * ca)
    ey = cy + int(length * sa)
    # perpendiculaire unitaire
    nx = int(-sa + 0.5); ny = int(ca + 0.5)
    offsets = [0] if thick == 1 else ([-1, 0, 1] if thick == 3 else [-1, 1])
    for off in offsets:
        buf.line(cx + off*nx, cy + off*ny,
                 ex + off*nx, ey + off*ny, color)

def draw_clock_direct(display, t):
    """
    Dessine l'horloge directement sur l'écran (pas de buffer).
    Efface d'abord le carré CLK_BX,CLK_BY..+_CS,+_CS puis trace.
    À 8 MHz SPI la zone 84×84 = ~14 ms : imperceptible.
    """
    cx = CLK_CX; cy = CLK_CY; r = CLK_R

    # ── Effacement zone horloge ─────────────────────────────────────────────
    display.fill_hrect(CLK_BX, CLK_BY, _CS, _CS, C_BLACK)

    # ── Fond disque ─────────────────────────────────────────────────────────
    display.fill_circle(cx, cy, r,     C_DKGRAY)
    display.draw_circle(cx, cy, r,     C_GRAY)

    # ── Graduations ─────────────────────────────────────────────────────────
    for i in range(60):
        a  = math.radians(i * 6)
        ca = math.cos(a); sa = math.sin(a)
        if i % 5 == 0:
            r1 = r - 11; r2 = r - 2; col = C_WHITE
        else:
            r1 = r - 5;  r2 = r - 2; col = C_GRAY
        display.draw_line(int(cx + r1*ca), int(cy + r1*sa),
                          int(cx + r2*ca), int(cy + r2*sa), col)

    h = t[3] % 12; m = t[4]; s = t[5]

    # ── Aiguille heures (blanche, 3 lignes parallèles) ──────────────────────
    ha = math.radians((h + m / 60.0) * 30 - 90)
    lh = int(r * 0.52)
    hx = int(cx + lh * math.cos(ha)); hy = int(cy + lh * math.sin(ha))
    px = int(-math.sin(ha) + 0.5);   py = int(math.cos(ha) + 0.5)
    for o in (-1, 0, 1):
        display.draw_line(cx+o*px, cy+o*py, hx+o*px, hy+o*py, C_WHITE)

    # ── Aiguille minutes (cyan, 2 lignes) ───────────────────────────────────
    ma = math.radians(m * 6 - 90)
    lm = int(r * 0.78)
    mx = int(cx + lm * math.cos(ma)); my = int(cy + lm * math.sin(ma))
    px = int(-math.sin(ma) + 0.5);   py = int(math.cos(ma) + 0.5)
    for o in (0, 1):
        display.draw_line(cx+o*px, cy+o*py, mx+o*px, my+o*py, C_CYAN)

    # ── Aiguille secondes (rouge + contre-poids) ────────────────────────────
    sa2 = math.radians(s * 6 - 90)
    ls  = int(r * 0.90); lq = int(r * 0.22)
    sx  = int(cx + ls * math.cos(sa2)); sy = int(cy + ls * math.sin(sa2))
    qx  = int(cx - lq * math.cos(sa2)); qy = int(cy - lq * math.sin(sa2))
    display.draw_line(cx, cy, sx, sy, C_RED)
    display.draw_line(cx, cy, qx, qy, C_RED)

    # ── Pivot central ────────────────────────────────────────────────────────
    display.fill_circle(cx, cy, 5, C_WHITE)
    display.fill_circle(cx, cy, 3, C_RED)


# ────────────────────────────────────────────────────────────────────────────
# DESSIN LUNE (direct sur display — mis à jour /60s seulement)
# ────────────────────────────────────────────────────────────────────────────
def draw_moon(display, cx, cy, r, phase):
    """
    Icône phase lunaire pixel par pixel.
    phase 0 = nouvelle lune, 0.5 = pleine lune.
    """
    cos_p  = math.cos(2 * math.pi * phase)
    waxing = (phase <= 0.5)
    for dy in range(-r, r + 1):
        xd = int(math.sqrt(max(0.0, float(r*r - dy*dy))))
        if xd == 0: continue
        xt = int(cos_p * xd)         # position du terminateur dans [-xd, xd]
        y  = cy + dy
        if waxing:
            dark_w = xt + xd
            lit_w  = xd - xt
            if dark_w > 0: display.draw_hline(cx - xd, y, dark_w, C_GRAY)
            if lit_w  > 0: display.draw_hline(cx + xt, y, lit_w,  C_WHITE)
        else:
            lit_w  = -xt + xd
            dark_w = xd - (-xt)
            if lit_w  > 0: display.draw_hline(cx - xd,    y, lit_w,  C_WHITE)
            if dark_w > 0: display.draw_hline(cx + (-xt), y, dark_w, C_GRAY)
    display.draw_circle(cx, cy, r, C_LTGRAY)


# ────────────────────────────────────────────────────────────────────────────
# FONCTIONS D'AFFICHAGE ÉCRAN
# ────────────────────────────────────────────────────────────────────────────
def draw_row(display, y0, y1, text, color, bg, bold=False):
    """
    Efface la ligne [y0..y1] avec bg, puis dessine 'text' centré.
    bold=True → double-passe décalée d'un pixel pour simuler le gras.
    """
    font = display._font
    display.fill_rectangle(0, y0, 320, y1 - y0 + 1, bg)
    if font is None or not text: return
    w   = font.measure_text(text)
    x   = max(0, (320 - w) // 2)
    ty  = y0 + (y1 - y0 - 24) // 2        # centrage vertical
    display.draw_text(x, ty, text, font, color, bg)
    if bold:
        display.draw_text(x + 1, ty, text, font, color, bg)


def draw_title(display):
    ville = global_state['config']['location'].get('ville', 'ESP32')
    draw_row(display, TY0, TY1, ville.upper(), C_CYAN, C_DKBLUE, bold=True)
    display.draw_hline(0, TY1, 320, C_BLUE)


def draw_datetime(display):
    """
    Ligne 2 : '14 JUILLET 2026 - 10:25:12'
    Appelée chaque seconde depuis la boucle principale.
    """
    t = global_state['local_time']
    if t is None: return
    # Date locale : t[2]=jour, t[1]=mois, t[0]=annee
    dt_str = "%d %s %d - %02d:%02d:%02d" % (
        t[2], _MOIS[t[1]], t[0], t[3], t[4], t[5])
    draw_row(display, DY0, DY1, dt_str, C_WHITE, C_DKGRAY)


def draw_tz(display):
    tz_h   = global_state['tz_offset'] // 3600
    tz_str = "(%s - UTC%+d)" % (global_state['tz_name'], tz_h)
    draw_row(display, ZY0, ZY1, tz_str, C_ORANGE, C_DKGRAY)


def draw_meteo(display):
    md   = global_state['meteo_data']
    temp = md.get('temp')
    hum  = md.get('hum')
    vit  = md.get('vent_vit')
    deg  = md.get('vent_dir')

    # Température
    ts = ("%.1f" % temp + "C") if temp is not None else "---C"

    # Humidité
    hs = ("%d%%" % int(round(hum))) if hum is not None else "---%"

    # Vitesse vent : entier si >= 10 km/h, sinon 1 décimale
    if vit is not None:
        vs = ("%.0f" % vit if vit >= 10.0 else "%.1f" % vit) + "km/h"
    else:
        vs = "--km/h"

    # Direction
    ds = wind_label(deg)

    meteo_str = ts + " - " + hs + " - " + vs + " " + ds
    draw_row(display, MY0, MY1, meteo_str, C_GREEN, C_BLACK)
    display.draw_hline(0, MY1, 320, C_GRAY)


def draw_gfx_static(display):
    """Fond + séparateur de la zone graphique (appelé une seule fois)."""
    display.fill_rectangle(0, GX0, 320, GX1 - GX0 + 1, C_BLACK)
    display.draw_vline(VSEP_X, GX0, GX1 - GX0, C_GRAY)


def draw_moon_zone(display):
    """Lune + nom de phase (appelé toutes les 60s)."""
    # Efface la zone lune
    display.fill_rectangle(VSEP_X + 1, GX0, 320 - VSEP_X - 1,
                           GX1 - GX0 + 1, C_BLACK)
    p, pname = moon_phase()
    draw_moon(display, MOON_CX, MOON_CY, MOON_R, p)
    # Nom de phase centré dans la zone droite [VSEP_X+1 .. 319]
    font = display._font
    if font:
        w  = font.measure_text(pname)
        x  = VSEP_X + 1 + max(0, (319 - VSEP_X - 1 - w) // 2)
        display.draw_text(x, MOON_TY, pname, font, C_LTGRAY, C_BLACK)


def update_time_and_clock(display):
    """Mise à jour chaque seconde : date/heure + horloge."""
    draw_datetime(display)
    t = global_state['local_time']
    if t:
        draw_clock_direct(display, t)


def draw_screen_full(display):
    """Redessin complet. Appelé au démarrage et toutes les 60s."""
    draw_title(display)
    draw_datetime(display)
    draw_tz(display)
    draw_meteo(display)
    draw_gfx_static(display)
    draw_moon_zone(display)
    # Horloge analogique directe
    t = global_state['local_time']
    if t:
        draw_clock_direct(display, t)


# ────────────────────────────────────────────────────────────────────────────
# CONFIG
# ────────────────────────────────────────────────────────────────────────────
async def load_config():
    try:
        with open('config.json', 'r') as f:
            global_state['config'] = json.load(f)
        c = global_state['config']
        sep("="); print("CONFIG CHARGEE")
        sep()
        print("  Cible : " + c.get('target', '?'))
        loc = c['location']
        print("  Ville : " + loc.get('ville','?') + " (" + loc.get('pays','?') + ")")
        print("  WiFi  : " + c['wifi']['ssid'])
        t = c['tft']
        print("  TFT   : " + str(t['width']) + "x" + str(t['height'])
              + "  rot=" + str(t['rotation']))
        print("  LED   : GPIO" + str(c.get('heartbeat_led',{}).get('pin','?')))
        sep("=")
    except Exception as e:
        print("config.json absent : " + str(e))
        global_state['config'] = DEFAULT_CONFIG
        await setup_ap_mode()

async def save_config():
    if global_state['config'].get('target') == "wokwi-esp32": return
    with open('config.json', 'w') as f: json.dump(global_state['config'], f)


# ────────────────────────────────────────────────────────────────────────────
# AP SETUP
# ────────────────────────────────────────────────────────────────────────────
async def setup_ap_mode():
    ap = network.WLAN(network.AP_IF)
    ap.active(True)
    ap.config(essid='ESP32-Setup', password='', authmode=network.AUTH_OPEN)
    print("[AP] http://192.168.4.1")

    async def handle(reader, writer):
        try:
            req = await reader.read(1024)
            rs  = req.decode('utf-8', 'ignore')
            if 'POST' in rs:
                body = rs[rs.find('\r\n\r\n') + 4:]
                p = {}
                for pair in body.split('&'):
                    if '=' in pair:
                        k, v = pair.split('=', 1)
                        p[k] = v.replace('+', ' ').strip()
                if 'ssid'  in p: global_state['config']['wifi']['ssid']      = p['ssid']
                if 'pass'  in p: global_state['config']['wifi']['password']   = p.get('pass','')
                if 'ville' in p: global_state['config']['location']['ville']  = p['ville']
                if 'pays'  in p: global_state['config']['location']['pays']   = p['pays']
                await save_config()
                writer.write(b"HTTP/1.1 200 OK\r\n\r\n<h2>OK - reboot...</h2>")
                await writer.drain()
                await asyncio.sleep(2); machine.reset()
            else:
                writer.write(
                    b"HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n\r\n"
                    b"<html><body><form method=POST>"
                    b"SSID<input name=ssid><br>"
                    b"MDP<input name=pass type=password><br>"
                    b"Ville<input name=ville><br>"
                    b"Pays (2 car.)<input name=pays maxlength=2><br>"
                    b"<button>OK</button></form></body></html>")
                await writer.drain()
        except: pass
        finally: writer.close(); await writer.wait_closed()

    server = await asyncio.start_server(handle, "0.0.0.0", 80)
    await server.wait_closed()


# ────────────────────────────────────────────────────────────────────────────
# GEOLOCALISATION
# ────────────────────────────────────────────────────────────────────────────
async def fetch_location():
    loc = global_state['config']['location']
    sep(); print("[GEO] Vérification coordonnées...")

    if loc['ville'] and loc['pays'] and (loc['latitude'] == 0 or loc['longitude'] == 0):
        url = ("https://nominatim.openstreetmap.org/search?q="
               + url_encode(loc['ville']) + "+" + url_encode(loc['pays'])
               + "&format=json&limit=1")
        print("[NOMINATIM] " + loc['ville'] + ", " + loc['pays'])
        try:
            resp = requests.get(url, headers={'User-Agent': 'ESP32-Meteo/1.0'})
            raw  = resp.text
            print("[NOMINATIM] " + str(len(raw)) + " oct. : " + raw[:80])
            data = json.loads(raw)
            if data:
                loc['latitude']  = float(data[0]['lat'])
                loc['longitude'] = float(data[0]['lon'])
                print("[NOMINATIM] lat=%.5f  lon=%.5f" % (loc['latitude'], loc['longitude']))
                await save_config()
            else:
                print("[NOMINATIM] Aucun résultat")
        except Exception as e:
            print("[NOMINATIM] Erreur : " + str(e))
            global_state['error'] = "Nominatim failed"
    else:
        print("[GEO] Coords : lat=" + str(loc['latitude']) + "  lon=" + str(loc['longitude']))

    print("[TZ] Offset sera extrait de la réponse Open-Meteo (utc_offset_seconds)")
    sep()


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE WIFI
# ────────────────────────────────────────────────────────────────────────────
async def task_wifi():
    wlan = network.WLAN(network.STA_IF)
    wlan.active(True)
    while True:
        if not wlan.isconnected():
            ssid = global_state['config']['wifi']['ssid']
            print("[WiFi] Connexion à '" + ssid + "'...")
            # Déconnecter proprement avant de reconnecter
            # (évite OSError "sta is connecting" si une tentative est en cours)
            try:
                wlan.disconnect()
            except Exception:
                pass
            await asyncio.sleep_ms(200)
            try:
                wlan.connect(ssid, global_state['config']['wifi']['password'])
            except OSError as e:
                print("[WiFi] connect() erreur : " + str(e))
                await asyncio.sleep(10)
                continue
            for _ in range(20):
                await asyncio.sleep(0.5)
                if wlan.isconnected(): break
            if wlan.isconnected():
                ip, mask, gw, dns = wlan.ifconfig()
                sep("="); print("[WiFi] CONNECTÉ  IP=" + ip + "  GW=" + gw); sep("=")
                global_state['wifi_connected'].set()
                global_state['error'] = None
            else:
                print("[WiFi] Échec connexion")
                global_state['error'] = "WiFi failed"
        await asyncio.sleep(30)   # 30s entre vérifications (était 15s → moins agressif)


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE NTP
# ────────────────────────────────────────────────────────────────────────────
async def task_ntp():
    await global_state['wifi_connected'].wait()
    # Retry rapide toutes les 10s jusqu'au 1er succès, puis toutes les 4h
    interval = 10
    while True:
        print("[NTP] Synchronisation (interval=%ds)..." % interval)
        try:
            ntptime.settime()
            t_utc = time.localtime()
            sep()
            print("[NTP] UTC : %04d-%02d-%02d  %02d:%02d:%02d" % t_utc[:6])
            sep()
            global_state['time_updated'].set()
            interval = 4 * 3600     # succès → resync dans 4h
        except Exception as e:
            print("[NTP] Echec : " + str(e) + "  retry dans %ds" % interval)
        await asyncio.sleep(interval)


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE MÉTÉO  (extrait aussi utc_offset_seconds pour l'heure locale)
# ────────────────────────────────────────────────────────────────────────────
async def task_meteo():
    while True:
        await global_state['wifi_connected'].wait()
        loc = global_state['config']['location']
        lat = loc.get('latitude', 0)
        lon = loc.get('longitude', 0)

        if lat == 0 or lon == 0:
            print("[Météo] Coordonnées absentes, attente 5 min")
            await asyncio.sleep(300)
            continue

        url = ("https://api.open-meteo.com/v1/forecast?"
               "latitude=%.4f&longitude=%.4f"
               "&current=temperature_2m,relative_humidity_2m,"
               "wind_speed_10m,wind_direction_10m,weather_code"
               "&timezone=auto") % (lat, lon)

        print("[Météo] Requête (%.3f, %.3f)..." % (lat, lon))
        try:
            resp = requests.get(url)
            if resp.status_code == 200:
                data  = resp.json()
                c     = data.get('current', {})

                global_state['meteo_data'] = {
                    'temp':     c.get('temperature_2m'),
                    'hum':      c.get('relative_humidity_2m'),
                    'vent_vit': c.get('wind_speed_10m'),
                    'vent_dir': c.get('wind_direction_10m'),
                    'wcode':    c.get('weather_code'),
                }

                # ── Fuseau horaire (DST inclus) ──────────────────────
                tz_sec  = data.get('utc_offset_seconds')
                tz_zone = data.get('timezone', '?')
                tz_abbr = data.get('timezone_abbreviation', 'UTC')
                if tz_sec is not None:
                    global_state['tz_offset'] = int(tz_sec)
                    global_state['tz_name']   = tz_abbr

                if not global_state['meteo_ready'].is_set():
                    global_state['meteo_ready'].set()

                md  = global_state['meteo_data']
                lbl = wind_label(md['vent_dir'])
                t_l = get_local_time()
                sep()
                print("[Météo] Données reçues")
                print("  Fuseau  : " + tz_zone + " (" + tz_abbr + ")")
                print("  Offset  : " + str(global_state['tz_offset'])
                      + "s (%+dh)" % (global_state['tz_offset'] // 3600))
                print("  Local   : %04d-%02d-%02d  %02d:%02d:%02d"
                      % (t_l[0],t_l[1],t_l[2], t_l[3],t_l[4],t_l[5]))
                print("  Temp    : " + (("%.1f C" % md['temp'])   if md['temp']     is not None else "---"))
                print("  Hum     : " + (("%d %%" % md['hum'])     if md['hum']      is not None else "---"))
                vit = md['vent_vit']
                print("  Vent    : " + (("%.1f km/h" % vit)       if vit            is not None else "---"))
                print("  Dir     : " + (("%d (%s)" % (int(md['vent_dir']), lbl)) if md['vent_dir'] is not None else "---"))
                p, pn = moon_phase()
                print("  Lune    : %.2f  %s" % (p, pn))
                sep()
            else:
                print("[Météo] HTTP " + str(resp.status_code))
                if not global_state['meteo_ready'].is_set():
                    global_state['meteo_ready'].set()
        except Exception as e:
            print("[Météo] Erreur : " + str(e))
            if not global_state['meteo_ready'].is_set():
                global_state['meteo_ready'].set()

        freq = global_state['config'].get('meteo_freq', 600)
        print("[Météo] Prochain relevé dans " + str(freq) + "s")
        await asyncio.sleep(freq)


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE AFFICHAGE
# ────────────────────────────────────────────────────────────────────────────
async def task_display():
    print("[DISPLAY] Init SPI + ILI9341...")
    tft = global_state['config']['tft']
    try:
        spi = SPI(1, baudrate=8000000, polarity=0, phase=0,
                  sck=Pin(tft['spi']['sck']),
                  mosi=Pin(tft['spi']['mosi']),
                  miso=Pin(tft['spi']['miso']))
        display = ili9341.Display(
            spi,
            cs=Pin(tft['pins']['cs']), dc=Pin(tft['pins']['dc']),
            rst=Pin(tft['pins']['rst']),
            width=tft['width'], height=tft['height'], rotation=tft['rotation'])
        print("[DISPLAY] ILI9341 OK  %dx%d" % (tft['width'], tft['height']))

        gc.collect()
        print("[DISPLAY] Pas de buffer (dessin direct) heap=%d" % gc.mem_free())

        # ── Police ──────────────────────────────────────────────────────────────
        gc.collect()
        try:
            font = XglcdFont('EspressoDolce18x24.c', 18, 24)
            print("[DISPLAY] Police chargée  heap=%d" % gc.mem_free())
        except Exception as e:
            print("[DISPLAY] Police : " + str(e)); font = None
        display._font = font

        # ── Écran de démarrage ───────────────────
        display.fill(C_NAVY)
        if font:
            ville = global_state['config']['location'].get('ville','ESP32')
            tw = font.measure_text(ville.upper())
            display.draw_text(max(0,(320-tw)//2), 80, ville.upper(), font, C_CYAN, C_NAVY)
            display.draw_text(60, 116, "Station Meteo", font, C_WHITE, C_NAVY)
            _lbl = ["WiFi...", "NTP...  ", "Meteo+TZ..."]
        else:
            _lbl = ["","",""]

        # ── Attentes séquentielles ───────────────
        def splash(msg):
            if font:
                display.fill_rectangle(0, 150, 320, 40, C_NAVY)
                display.draw_text(max(0,(320-font.measure_text(msg))//2),
                                  154, msg, font, C_YELLOW, C_NAVY)

        splash(_lbl[0])
        await global_state['wifi_connected'].wait()
        splash(_lbl[1])
        # NTP en tâche de fond — on n'attend pas (peut timeout sur Wokwi)
        # L'heure sera correcte dès que NTP sync ; en attendant UTC+offset suffit
        splash(_lbl[2])
        # 1er relevé météo → offset TZ connu → heure locale correcte
        await global_state['meteo_ready'].wait()

        global_state['local_time'] = get_local_time()
        t = global_state['local_time']
        print("[DISPLAY] TZ=%s  offset=%ds  local=%02d:%02d:%02d"
              % (global_state['tz_name'], global_state['tz_offset'],
                 t[3], t[4], t[5]))

        # ── Affichage initial complet ────────────
        draw_screen_full(display)

        tick = 0
        while True:
            global_state['local_time'] = get_local_time()
            t = global_state['local_time']

            if font:
                if tick % 60 == 0 and tick > 0:
                    # Redessin complet : météo + lune + statique
                    draw_screen_full(display)
                    print("[DISPLAY] Full redraw  %02d:%02d" % (t[3], t[4]))
                else:
                    # Chaque seconde : datetime + horloge (dessin direct)
                    draw_datetime(display)
                    draw_clock_direct(display, t)

            tick += 1
            await asyncio.sleep(1)

    except Exception as e:
        print("[DISPLAY] CRASH : " + str(e))
        import sys; sys.print_exception(e)
        while True: await asyncio.sleep(5)


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE WEB  — serveur JSON + page HTML+JS autonome
# ────────────────────────────────────────────────────────────────────────────

# Page HTML intégrée. Le JS gère horloge (locale via tz_offset) et
# rafraîchit les données météo toutes les 30 s, sans recharger la page.
_HTML = (
    "<!DOCTYPE html><html lang='fr'><head><meta charset='utf-8'>"
    "<meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>Station Meteo</title><style>"
    "body{background:#00091e;color:#fff;font-family:'Courier New',monospace;"
    "text-align:center;padding:20px;max-width:480px;margin:0 auto}"
    "h1{color:#00d2d2;letter-spacing:3px;font-size:1.3em;margin:6px 0}"
    "#dt{color:#fff;font-size:1.7em;font-weight:bold;margin:8px 0}"
    "#tz{color:#ff9100;font-size:.9em;margin:4px 0}"
    "#meteo{color:#37d257;font-size:1.15em;margin:12px 0}"
    "#moon{color:#aaa;font-size:.95em;margin:8px 0}"
    ".dot{display:inline-block;width:10px;height:10px;border-radius:50%;"
    "margin-right:4px;vertical-align:middle}"
    ".ok{background:#37d257}.err{background:#dc3737}"
    "#stat{font-size:.75em;color:#555;margin-top:18px}"
    "</style></head><body>"
    "<h1 id='ville'>---</h1>"
    "<div id='dt'>--/-- -- --:--:--</div>"
    "<div id='tz'>---</div>"
    "<div id='meteo'>---</div>"
    "<div id='moon'>---</div>"
    "<div id='stat'>"
    "<span class='dot ok' id='dw'></span>WiFi&nbsp;"
    "<span class='dot ok' id='dn'></span>NTP"
    "</div>"
    "<script>"
    "const MOIS=['','Janvier','Fevrier','Mars','Avril','Mai','Juin',"
    "'Juillet','Aout','Septembre','Octobre','Novembre','Decembre'];"
    "const MOON_NAMES=['Nvlle lune','Crois.croi','1er quart.','Gibb.croi.',"
    "'Plne lune ','Gibb.decr.','Der.quart.','Crois.decr'];"
    "let tzOff=0;"
    "function pad(n){return n<10?'0'+n:''+n}"
    "function moonPhase(){"
    "const NM=947182440000,SYN=29.530588*86400000;"
    "const p=((Date.now()-NM)%SYN)/SYN;"
    "return MOON_NAMES[Math.min(7,Math.floor(p*8))]+' ('+(p*100|0)+'%)'}"
    "function tick(){"
    "const ms=Date.now()+tzOff*1000;"
    "const d=new Date(ms);"
    "const day=d.getUTCDate();"
    "const mo=MOIS[d.getUTCMonth()+1];"
    "const yr=d.getUTCFullYear();"
    "const hh=pad(d.getUTCHours());"
    "const mm=pad(d.getUTCMinutes());"
    "const ss=pad(d.getUTCSeconds());"
    "document.getElementById('dt').textContent="
    "day+' '+mo+' '+yr+' - '+hh+':'+mm+':'+ss;"
    "document.getElementById('moon').textContent='Lune : '+moonPhase()}"
    "async function fetchData(){"
    "try{"
    "const r=await fetch('/api');"
    "const d=await r.json();"
    "tzOff=d.tz_offset||0;"
    "document.getElementById('ville').textContent=(d.ville||'').toUpperCase();"
    "document.getElementById('tz').textContent='('+d.tz_name+' - UTC'+(tzOff>=0?'+':'')"
    "+(tzOff/3600|0)+'h)';"
    "const vs=d.vit!=null?(d.vit>=10?Math.round(d.vit).toString():"
    "d.vit.toFixed(1)):'-';"
    "document.getElementById('meteo').textContent="
    "(d.temp!=null?d.temp.toFixed(1):'--')+'C - '"
    "+(d.hum!=null?d.hum+'%':'--')+'% - '+vs+'km/h '+d.dir;"
    "document.getElementById('dw').className='dot '+(d.wifi?'ok':'err');"
    "document.getElementById('dn').className='dot '+(d.ntp?'ok':'err');"
    "}catch(e){document.getElementById('stat').textContent='Erreur: '+e.message}}"
    "setInterval(tick,1000);tick();"
    "fetchData();setInterval(fetchData,30000);"
    "</script></body></html>"
)

def _api_json():
    """Construit la réponse JSON pour /api."""
    md  = global_state['meteo_data']
    lt  = global_state['local_time']
    deg = md.get('vent_dir')
    vit = md.get('vent_vit')
    return ('{"ville":"%s","tz_name":"%s","tz_offset":%d,'
            '"temp":%s,"hum":%s,"vit":%s,"dir":"%s",'
            '"wifi":%s,"ntp":%s}') % (
        global_state['config']['location'].get('ville',''),
        global_state['tz_name'],
        global_state['tz_offset'],
        ("%.1f" % md['temp'])           if md.get('temp')     is not None else "null",
        ("%d"   % int(md['hum']))        if md.get('hum')      is not None else "null",
        ("%.1f" % vit)                   if vit                is not None else "null",
        wind_label(deg),
        "true" if global_state['wifi_connected'].is_set() else "false",
        "true" if global_state['time_updated'].is_set()   else "false",
    )

async def task_web():
    if global_state['config'].get('target') == "wokwi-esp32":
        print("[WEB] Désactivé sur Wokwi")
        return

    async def handler(reader, writer):
        try:
            req  = await reader.read(1024)
            line = req.decode('utf-8','ignore').split('\r\n')[0]   # "GET /path HTTP/1.1"
            path = line.split(' ')[1] if len(line.split(' ')) > 1 else '/'

            if path == '/api':
                body = _api_json()
                resp = ("HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n"
                        "Access-Control-Allow-Origin: *\r\n"
                        "Content-Length: %d\r\n\r\n") % len(body)
                writer.write(resp.encode() + body.encode())
            else:
                resp = ("HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\n"
                        "Content-Length: %d\r\n\r\n") % len(_HTML)
                writer.write(resp.encode() + _HTML.encode())

            await writer.drain()
        except Exception as e:
            print("[WEB] " + str(e))
        finally:
            writer.close(); await writer.wait_closed()

    try:
        print("[WEB] Serveur HTTP sur port 80")
        server = await asyncio.start_server(handler, "0.0.0.0", 80)
        await server.wait_closed()
    except Exception as e:
        print("[WEB] Erreur serveur : " + str(e))


# ────────────────────────────────────────────────────────────────────────────
# TÂCHE LED  (GPIO standard OU NeoPixel selon config)
# ────────────────────────────────────────────────────────────────────────────
async def task_led():
    # La LED fonctionne sur vrai matériel comme sur Wokwi (si composant présent).
    # Pas de blocage sur target : le GPIO inactif est sans danger sur Wokwi.
    led_cfg = global_state['config'].get('heartbeat_led', {})
    pin_n   = led_cfg.get('pin', 21)
    is_neo  = led_cfg.get('neopixel', False)

    if is_neo:
        # ── NeoPixel WS2812B ────────────────────
        try:
            import neopixel
            np = neopixel.NeoPixel(Pin(pin_n, Pin.OUT), 1)
        except Exception as e:
            print("[LED] NeoPixel init échoué : " + str(e))
            while True: await asyncio.sleep(5)

        C_OK=(0,40,0); C_OFF=(0,0,0); C_SOS=(60,0,0); C_ERR=(60,60,0)

        async def sos():
            for dur, col in [
                (200,C_SOS),(400,C_OFF),(200,C_SOS),(400,C_OFF),(200,C_SOS),(600,C_OFF),
                (600,C_SOS),(400,C_OFF),(600,C_SOS),(400,C_OFF),(600,C_SOS),(1400,C_OFF),
                (200,C_SOS),(400,C_OFF),(200,C_SOS),(400,C_OFF),(200,C_SOS),(2000,C_OFF)]:
                np[0]=col; np.write(); await asyncio.sleep_ms(dur)

        while True:
            err = global_state.get('error') or ''
            if 'wifi' in err.lower(): await sos()
            elif err:
                for _ in range(4):
                    np[0]=C_ERR; np.write(); await asyncio.sleep_ms(120)
                    np[0]=C_OFF; np.write(); await asyncio.sleep_ms(120)
                await asyncio.sleep_ms(800)
            else:
                np[0]=C_OK;  np.write(); await asyncio.sleep_ms(500)
                np[0]=C_OFF; np.write(); await asyncio.sleep_ms(500)
            await asyncio.sleep_ms(50)

    else:
        # ── LED standard (GPIO logique) ─────────
        # Impulsion courte 100ms toutes les 1s = OK
        # Clignotement rapide = erreur
        print("[LED] GPIO%d standard" % pin_n)
        try:
            led = Pin(pin_n, Pin.OUT, value=0)
        except Exception as e:
            print("[LED] Erreur init : " + str(e))
            while True: await asyncio.sleep(5)

        while True:
            err = global_state.get('error') or ''
            if err:
                # Clignotement rapide 5 Hz (erreur)
                led.value(1); await asyncio.sleep_ms(100)
                led.value(0); await asyncio.sleep_ms(100)
            else:
                # Battement 1 Hz : impulsion courte + longue pause
                led.value(1); await asyncio.sleep_ms(80)
                led.value(0); await asyncio.sleep_ms(920)


# ────────────────────────────────────────────────────────────────────────────
# MODE TEST SYNCHRONE (MODE_TEST = True)
# ────────────────────────────────────────────────────────────────────────────
def test_ecran_sync():
    print("=== MODE TEST ===")
    try:
        tft = DEFAULT_CONFIG['tft']
        spi = SPI(1, baudrate=8000000, polarity=0, phase=0,
                  sck=Pin(tft['spi']['sck']),
                  mosi=Pin(tft['spi']['mosi']),
                  miso=Pin(tft['spi']['miso']))
        d = ili9341.Display(
            spi, cs=Pin(tft['pins']['cs']), dc=Pin(tft['pins']['dc']),
            rst=Pin(tft['pins']['rst']),
            width=tft['width'], height=tft['height'], rotation=tft['rotation'])
        d.fill(C_BLACK)
        d.draw_rectangle(20, 80, 280, 80, C_RED)
        print("Test rectangle rouge OK")
    except Exception as e:
        print("ERREUR : " + str(e))
        import sys; sys.print_exception(e)
    while True: time.sleep(1)


# ────────────────────────────────────────────────────────────────────────────
# MAIN
# ────────────────────────────────────────────────────────────────────────────
async def main():
    sep("="); print("   ESP32 METEO — Démarrage"); sep("=")
    await load_config()

    # WiFi en premier (évite deadlock sur wifi_connected.wait)
    wifi_task = asyncio.create_task(task_wifi())

    if global_state['config']['wifi']['ssid']:
        await global_state['wifi_connected'].wait()
        await fetch_location()

    print("[MAIN] Lancement des tâches...")
    await asyncio.gather(
        wifi_task,
        asyncio.create_task(task_ntp()),
        asyncio.create_task(task_meteo()),
        asyncio.create_task(task_display()),
        asyncio.create_task(task_web()),
        asyncio.create_task(task_led())
    )

# ────────────────────────────────────────────────────────────────────────────
if MODE_TEST:
    test_ecran_sync()
else:
    asyncio.run(main())