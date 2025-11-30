const cacheName = "maytinh-v1";

self.addEventListener("install", (e) => {
  e.waitUntil(
    caches.open(cacheName).then((cache) => {
      return cache.addAll([
        "/",           // trang chủ
        "/index.html",
        "/style.css",
        "/script.js",
        // thêm tất cả file bạn có ở đây
      ]);
    })
  );
});

self.addEventListener("fetch", (e) => {
  e.respondWith(
    caches.match(e.request).then((response) => {
      return response || fetch(e.request);
    })
  );
});
