/*
 * Copyright 2014 Google Inc.
 *
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE file.
 */

// running create_test_font_color generates ./<cbdt|sbix|cpal>.ttx
// which are read by fonttools ttx to produce native fonts.

#include "src/base/SkAutoMalloc.h"
#include "include/core/SkRefCnt.h"
#include "include/core/SkStream.h"
#include "include/core/SkString.h"
#include "include/core/SkCanvas.h"
#include "include/core/SkFontMgr.h"
#include "include/core/SkSurface.h"
#include "include/core/SkFont.h"
#include "include/core/SkFontStyle.h"
#include "include/core/SkColorSpace.h"
#include "include/core/SkTextBlob.h"
#include "include/core/SkBitmap.h"
#include "tools/flags/CommandLineFlags.h"
#include "tools/fonts/TestSVGTypeface.h"
#include "tools/window/RasterWindowContext.h"
#include "tools/fonts/FontToolUtils.h"
#include "modules/skparagraph/src/ParagraphBuilderImpl.h"
#include "modules/skparagraph/src/Run.h"
#include "modules/skparagraph/src/TextWrapper.h"
#include "modules/skparagraph/src/ParagraphImpl.h"
#include "modules/skparagraph/include/FontCollection.h"
#include "modules/skparagraph/include/ParagraphStyle.h"
#include "modules/skparagraph/include/Paragraph.h"
#include "Windows.h"
#include <cmath>

#pragma comment(lib, "skparagraph")

#if defined(SK_ENABLE_SVG)

static SkAutoMalloc globalSurfaceMemory;
const char* g_sWindowClass = "FirstSkiaApp";
LRESULT CALLBACK WndProc(HWND hWnd, UINT message, WPARAM wParam, LPARAM lParam)
{
	bool eventHandled = false;
	switch (message)
	{
	case WM_PAINT:
	{
		PAINTSTRUCT ps;
		BeginPaint(hWnd, &ps);
		EndPaint(hWnd, &ps);
		eventHandled = true;
		break;
	}

	case WM_DESTROY:
		PostQuitMessage(0);
		eventHandled = true;
		break;

	case WM_CLOSE:
		DestroyWindow(hWnd);
		eventHandled = true;
		break;

	case WM_SIZE:
		eventHandled = true;
		break;

	case WM_KEYDOWN:
	case WM_SYSKEYDOWN:
		break;

	case WM_KEYUP:
	case WM_SYSKEYUP:
		break;

	case WM_LBUTTONDOWN:
	case WM_LBUTTONUP: 
		break;

	case WM_MOUSEMOVE:
		break;

	case WM_MOUSEWHEEL:
		break;
	}

	return DefWindowProc(hWnd, message, wParam, lParam);
}

static HWND MakeWindow(int w, int h)
{
    HWND result;
    static WNDCLASSEX wcex;
    static bool wcexInit = false;

    if (!wcexInit) {
        wcex.cbSize = sizeof(WNDCLASSEX);

        wcex.style = CS_HREDRAW | CS_VREDRAW | CS_OWNDC;
        wcex.lpfnWndProc = WndProc;
        wcex.cbClsExtra = 0;
        wcex.cbWndExtra = 0;
        wcex.hInstance = GetModuleHandle(nullptr);
        wcex.hIcon = LoadIcon(wcex.hInstance, (LPCTSTR)IDI_WINLOGO);
        wcex.hCursor = LoadCursor(nullptr, IDC_ARROW);
        wcex.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
        wcex.lpszMenuName = nullptr;
        wcex.lpszClassName = (const WCHAR*)g_sWindowClass;
        wcex.hIconSm = LoadIcon(wcex.hInstance, (LPCTSTR)IDI_WINLOGO);

        if (RegisterClassEx(&wcex)) wcexInit = true;
    }

    result = CreateWindow((const WCHAR*)g_sWindowClass,
                          nullptr,
                          WS_OVERLAPPEDWINDOW,
                          0,
                          0,
                          w,
                          h,
                          nullptr,
                          nullptr,
                          wcex.hInstance,
                          nullptr);

    //SetWindowLongPtr(result, GWLP_USERDATA, (LONG_PTR)application);

    return result;
}

static auto ResizeFrameBuffer(int w, int h) 
{
    const size_t bmpSize = sizeof(BITMAPINFOHEADER) + (h * (w * sizeof(uint32_t)));
    globalSurfaceMemory.reset(bmpSize);
    BITMAPINFO* bmpInfo = reinterpret_cast<BITMAPINFO*>(globalSurfaceMemory.get());
    ZeroMemory(bmpInfo, sizeof(BITMAPINFO));
    bmpInfo->bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmpInfo->bmiHeader.biWidth = w;
    bmpInfo->bmiHeader.biHeight = -h; // negative means top-down bitmap. Skia draws top-down.
    bmpInfo->bmiHeader.biPlanes = 1;
    bmpInfo->bmiHeader.biBitCount = 32;
    bmpInfo->bmiHeader.biCompression = BI_RGB;
    //globalPixels = (unsigned char*)bmpInfo->bmiColors;

    SkImageInfo info = SkImageInfo::Make(w, h, kBGRA_8888_SkColorType, kPremul_SkAlphaType);

    return SkCanvas::MakeRasterDirect(info, bmpInfo->bmiColors, w * sizeof(uint32_t));
}

static void SwapFrameBuffers(HWND window) 
{
    BITMAPINFO* bmpInfo = reinterpret_cast<BITMAPINFO*>(globalSurfaceMemory.get());
    HDC dc = GetDC(window);
    if (dc == 0) return;
	StretchDIBits(dc, 0, 0, bmpInfo->bmiHeader.biWidth, -bmpInfo->bmiHeader.biHeight, 0, 0,
                  bmpInfo->bmiHeader.biWidth,
                  -bmpInfo->bmiHeader.biHeight,
                  bmpInfo->bmiColors,
		          bmpInfo, DIB_RGB_COLORS, SRCCOPY);
    ReleaseDC(window, dc);
}

static void DrawString(SkCanvas* canvas, SkFont* font, SkPaint* paint, const char* string, SkScalar x, SkScalar y) 
{
    canvas->drawString(string, x, y, *font, *paint);
}

static const char* MaxStr(const char** texts, size_t count) 
{ 
    if (count == 0 || !texts) 
        return nullptr;

    const char* result = texts[0];
    for (size_t i = 0; i < count; ++i)
        result = strlen(result) < strlen(texts[i]) ? texts[i] : result;

    return result; 
}

#define ArrayCount(a) sizeof((a)) / sizeof(*(a))

static void DrawColor(SkCanvas* canvas, SkColor4f color) 
{
    canvas->clear(color);
}

static void DrawEverything(SkCanvas* canvas, const char** texts, size_t textCount) 
{
    const auto timesTypeface = ToolUtils::CreateTestTypeface("Times", SkFontStyle{});
    const auto georgiaTypeface = ToolUtils::CreateTestTypeface("Georgia", SkFontStyle{});
    constexpr SkScalar fontHeight = 30.0f;
    constexpr SkScalar fontStartX = 10.0f;
    constexpr SkScalar fontStartY = 50.0f;
    SkFont timesFont(timesTypeface, fontHeight);
    SkFont georgiaFont(georgiaTypeface, fontHeight);

    SkPaint paint;
    paint.setAntiAlias(true);
    paint.setColor(SkColorSetARGB(0xff, 0xdd, 0x12, 0xaa));
    paint.setStyle(SkPaint::kFill_Style);

    DrawString(canvas, &timesFont, &paint, texts[2], fontStartX, fontStartY);
    DrawString(canvas, &timesFont, &paint, texts[0], fontStartX, fontStartY + fontHeight);
    DrawString(canvas, &timesFont, &paint, texts[1], fontStartX, fontStartY + fontHeight * 2);

    const char* text = MaxStr(texts, textCount);
    SkScalar xOffset = timesFont.measureText(text, strlen(text), SkTextEncoding::kUTF8);

    // Add a gap for the next text column
    xOffset += fontStartX;

    paint.setColor(SkColorSetARGB(0xff, 0xaa, 0x66, 0xbb));

    DrawString(canvas, &georgiaFont, &paint, texts[2], xOffset, fontStartY);
    DrawString(canvas, &georgiaFont, &paint, texts[1], xOffset, fontStartY + fontHeight);
    DrawString(canvas, &georgiaFont, &paint, texts[0], xOffset, fontStartY + fontHeight * 2);

    text = MaxStr(texts, ArrayCount(texts));
    xOffset = georgiaFont.measureText(text, strlen(text), SkTextEncoding::kUTF8);
}


int main(int argc, char** argv) {
    constexpr int w = 800, h = 600;

    sk_sp<skia::textlayout::FontCollection> fontCollection = sk_make_sp<skia::textlayout::FontCollection>();
    fontCollection->setDefaultFontManager(ToolUtils::TestFontMgr());
    auto paraBuilder = skia::textlayout::ParagraphBuilderImpl::make({}, fontCollection);

    const char* texts[] = {"Vihma on.", "Hello Vihma on bigass world.", "Bigass and fatass."};

    for (size_t i = 0; i < ArrayCount(texts); ++i) 
        paraBuilder->addText(texts[i]);

    auto built = paraBuilder->Build();
    skia::textlayout::ParagraphImpl* paragraph = reinterpret_cast<skia::textlayout::ParagraphImpl*>(built.get());

    paragraph->layout(w);

    auto canvas = ResizeFrameBuffer(w, h);
    if (!globalSurfaceMemory.get()) return -1;

    HWND window = MakeWindow(w, h);
    if (ShowWindow(window, SW_SHOW)) return -1;

    MSG msg;
    memset(&msg, 0, sizeof(msg));
    while (WM_QUIT != msg.message) {
		while (PeekMessage(&msg, 0, 0, 0, PM_REMOVE))
		{
			TranslateMessage(&msg);
			DispatchMessage(&msg);
		}

        DrawColor(canvas.get(), SkColors::kLtGray);
        DrawEverything(canvas.get(), texts, ArrayCount(texts));
        SwapFrameBuffers(window);
    }

	return 0;
}

#else

#endif // SK_ENABLE_SVG
