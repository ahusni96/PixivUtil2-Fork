#!/usr/bin/env python3
"""Check whether pixiv or FANBOX accept your browser cookies, independent of PixivUtil2.

Usage (Windows example):
    1. In Firefox, log in to the site, open DevTools -> Network, reload, click the request
       for the page (www.pixiv.net or www.fanbox.cc) and copy the whole value of the
       "Cookie" request header into a text file, e.g. cookie.txt
       (keep this file private and delete it afterwards).
    2. Get the exact User-Agent of that same Firefox (console: navigator.userAgent).
    3. Run:
         python pixiv_cookie_check.py --cookie-file cookie.txt --ua "Mozilla/5.0 (...) Firefox/xxx.0"
       or for FANBOX (also calls the API the way PixivUtil2 does):
         python pixiv_cookie_check.py --site fanbox --cookie-file fanbox_cookie.txt --ua "..."

Optional:
    --only PHPSESSID,cf_clearance   send only these cookies (to see which ones matter)
    --impersonate firefox135        curl_cffi browser fingerprint (default firefox135)
    --proxy http://host:port        use a proxy (must be the same IP you got the cookie on)

Requires: pip install curl_cffi
Cookie values are never printed, only their names.
Note: cf_clearance is per site. pixiv.net and fanbox.cc each need their own, copied from
a request to that site.
"""
import argparse
import json
import re
import sys

from curl_cffi import requests

SITES = {
    "pixiv": {"url": "https://www.pixiv.net/", "referer": "https://www.pixiv.net"},
    "fanbox": {"url": "https://www.fanbox.cc/", "referer": "https://www.fanbox.cc/",
               "api": "https://api.fanbox.cc/creator.listFollowing"},
}
FANBOX_USER_FLAG = r'"user"\s*:\s*\{\s*"isLoggedIn"\s*:\s*(true|false)'


def parse_cookie_header(raw):
    raw = raw.strip().strip('"\'')
    if raw.lower().startswith("cookie:"):
        raw = raw[len("cookie:"):].strip()
    cookies = {}
    for part in raw.replace("\n", ";").split(";"):
        if "=" not in part:
            continue
        name, value = part.split("=", 1)  # values may contain '='
        name = name.strip()
        if name:
            cookies[name] = value.strip()
    return cookies


def save_page(page):
    print("RESULT: unrecognised page. Saving it to pixiv_check_page.html for inspection (may contain account details).")
    with open("pixiv_check_page.html", "w", encoding="utf-8") as fh:
        fh.write(page)
    return 3


def check_fanbox_api(args, cookies, kwargs):
    """ Call the FANBOX API the way PixivUtil2 does. Returns True if it answered with JSON. """
    api_kwargs = dict(kwargs)
    api_kwargs["headers"] = {"User-Agent": args.ua, "Referer": "https://www.fanbox.cc/", "Origin": "https://www.fanbox.cc",
                             "Accept": "application/json, text/plain, */*"}
    r = requests.get(args.api_url or SITES["fanbox"]["api"], **api_kwargs)
    has_body = False
    try:
        has_body = "body" in json.loads(r.text)
    except ValueError:
        pass
    print(f"api status        : {r.status_code}")
    print(f"api JSON w/ body  : {has_body}")
    print(f"api cf-mitigated  : {r.headers.get('cf-mitigated', '')}")
    return r.status_code == 200 and has_body


def main():
    ap = argparse.ArgumentParser(description="Check whether pixiv/FANBOX treat your cookies as logged in.")
    ap.add_argument("--site", choices=sorted(SITES), default="pixiv", help="which site to check (default: pixiv)")
    ap.add_argument("--cookie-file", required=True, help="text file with the Cookie header copied from your browser")
    ap.add_argument("--ua", required=True, help="exact User-Agent string of that same browser")
    ap.add_argument("--impersonate", default="firefox135", help="curl_cffi fingerprint (default: firefox135)")
    ap.add_argument("--only", help="comma-separated cookie names to send (default: all)")
    ap.add_argument("--url", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--api-url", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--proxy", help="proxy URL, e.g. http://127.0.0.1:8080")
    args = ap.parse_args()
    site = SITES[args.site]

    with open(args.cookie_file, encoding="utf-8") as fh:
        cookies = parse_cookie_header(fh.read())
    if args.only:
        wanted = {n.strip() for n in args.only.split(",")}
        cookies = {k: v for k, v in cookies.items() if k in wanted}

    print(f"site              : {args.site}")
    print(f"cookie names sent : {sorted(cookies)}")
    if args.site == "fanbox":
        print(f"FANBOXSESSID present : {'FANBOXSESSID' in cookies}")
    else:
        print(f"PHPSESSID present : {'PHPSESSID' in cookies}")
    print(f"cf_clearance      : {'cf_clearance' in cookies}")
    print(f"device_token      : {'device_token' in cookies}")
    print(f"impersonate       : {args.impersonate}")
    print(f"user-agent        : {args.ua}")

    kwargs = dict(impersonate=args.impersonate,
                  headers={"User-Agent": args.ua, "Referer": site["referer"]},
                  cookies=cookies, timeout=30)
    if args.proxy:
        kwargs["proxies"] = {"http": args.proxy, "https": args.proxy}

    r = requests.get(args.url or site["url"], **kwargs)
    page = r.text
    title = re.search(r"<title[^>]*>(.*?)</title>", page, re.S | re.I)
    login = re.search(r"dataLayer\s*=\s*\[\s*\{\s*login\s*:\s*['\"](\w+)['\"]", page)
    flags = re.findall(r'"isLoggedIn"\s*:\s*(true|false)', page)
    fanbox_flag = re.search(FANBOX_USER_FLAG, page)
    set_names = sorted({c.name for c in r.cookies.jar})

    print()
    print(f"status            : {r.status_code}")
    print(f"final url         : {r.url}")
    print(f"page length       : {len(page)}")
    print(f"title             : {title.group(1).strip()[:80] if title else None!r}")
    if args.site == "fanbox":
        print(f"user.isLoggedIn   : {fanbox_flag.group(1) if fanbox_flag else None}")
    else:
        print(f"dataLayer login   : {login.group(1) if login else None}")
        print(f"isLoggedIn flags  : {flags}")
    print(f"cf-mitigated      : {r.headers.get('cf-mitigated', '')}")
    print(f"cookies set by server: {set_names}")
    print()

    if (r.status_code in (403, 429) or "cf-chl" in page or "Just a moment" in page
            or "challenge_basic_security_FANBOX" in page):
        print("RESULT: blocked by Cloudflare. cf_clearance is missing/expired, or the user-agent / IP / "
              "fingerprint doesn't match the browser you copied it from.")
        if args.site == "fanbox":
            print("        FANBOX needs its own cf_clearance, copied from a request to www.fanbox.cc.")
        return 2

    if args.site == "fanbox":
        if fanbox_flag and fanbox_flag.group(1) == "true":
            print("page check        : FANBOX accepts these cookies (logged in).")
            print()
            if check_fanbox_api(args, cookies, kwargs):
                print()
                print("RESULT: FANBOX accepts these cookies for the page and the API (logged in).")
                print("        If PixivUtil2 still fails, the problem is in how PixivUtil2 loads the cookie.")
                return 0
            print()
            print("RESULT: the page accepts the cookies but the API call failed. api.fanbox.cc may need a")
            print("        cf_clearance of its own, so copy the Cookie header from a request to api.fanbox.cc")
            print("        (Network tab, filter 'api.fanbox.cc') and try again.")
            return 4
        if fanbox_flag and fanbox_flag.group(1) == "false":
            print("RESULT: FANBOX treats this request as LOGGED OUT.")
            print("        Check: the cookie includes FANBOXSESSID (Network tab, not document.cookie, which hides")
            print("        HttpOnly cookies), you are on the same IP as that browser, and you haven't logged out")
            print("        since copying it. If 'cookies set by server' lists FANBOXSESSID, the server rejected")
            print("        the session and issued a new one.")
            return 1
        return save_page(page)

    if (login and login.group(1) == "yes") or "true" in flags:
        print("RESULT: pixiv accepts these cookies from this script (logged in).")
        print("        If PixivUtil2 still fails, the problem is in how PixivUtil2 loads the cookie.")
        return 0
    if (login and login.group(1) == "no") or "false" in flags:
        print("RESULT: pixiv treats this request as LOGGED OUT.")
        print("        The cookies were sent but not accepted. Check: the cookie was copied from a logged-in")
        print("        request (Network tab, not document.cookie, which hides HttpOnly cookies), it includes")
        print("        PHPSESSID, you are on the same IP as that browser, and the session hasn't been")
        print("        logged out or rotated since. If 'cookies set by server' lists PHPSESSID, the server")
        print("        rejected the session and issued a new one.")
        return 1
    return save_page(page)


if __name__ == "__main__":
    sys.exit(main())
