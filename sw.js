/* 千里眼将棋 — このサービスワーカーは、ページを「クロスオリジン分離」するためのヘッダーを足すだけのもの。
   分離されたページでは SharedArrayBuffer が使えるので、千里眼が複数の CPU コアで同時に読めるようになる。
   何もキャッシュしない。うまく動かない環境では、これまでどおり 1 コアで読む。 */
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (e) => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', (e) => {
  const r = e.request;
  if (r.method !== 'GET' || new URL(r.url).origin !== self.location.origin) return;   // よそのサイト（フォント）には触らない
  if (r.cache === 'only-if-cached' && r.mode !== 'same-origin') return;
  e.respondWith(fetch(r).then((res) => {
    if (!res || res.status === 0 || res.type === 'opaque' || res.type === 'opaqueredirect') return res;
    try {
      const h = new Headers(res.headers);
      h.set('Cross-Origin-Opener-Policy', 'same-origin');
      h.set('Cross-Origin-Embedder-Policy', 'require-corp');
      return new Response(res.body, { status: res.status, statusText: res.statusText, headers: h });
    } catch (err) { return res; }
  }));
});
