"""Browser smoke checks for both languages, interactions, and narrow layouts.

Requires the optional Python playwright package and its Chromium browser.
Run while `npm run dev` serves localhost:5173.
"""
from pathlib import Path
import json
from playwright.sync_api import sync_playwright, expect

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'playwright-artifacts'
ARTIFACTS.mkdir(exist_ok=True)
BLUEPRINT = json.loads((ROOT / 'web/blueprint-data.json').read_text(encoding='utf-8'))


with sync_playwright() as playwright:
    browser = playwright.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1440, 'height': 1000}, device_scale_factor=1)
    errors = []
    page.on('pageerror', lambda error: errors.append(str(error)))
    response = page.goto('http://localhost:5173', wait_until='networkidle')
    assert response.status == 200
    expect(page.locator('.result-card')).to_have_count(4)
    expect(page.locator('#blueprint-workbench')).to_have_attribute('aria-busy', 'false')
    expect(page.locator('[data-result="kahn-kalai"]')).to_be_visible()
    expect(page.locator('.result-card').first).to_contain_text('Kahn-Kalai Conjecture (Park-Pham Theorem)')
    assert 'one conversation' not in page.locator('body').inner_text().lower()
    expect(page.locator('[data-i18n="stripPerspectives"]')).to_have_text('Intuition meetsformal proof')
    expect(page.locator('#detail-title')).to_have_text('Two notions of smallness, one bridge.')
    expect(page.locator('#about-heading')).to_have_text('A readable path from idea to verified statement.')
    expect(page.locator('.approach-grid article').nth(0)).to_contain_text('four formalization collections')
    expect(page.locator('.approach-grid article').nth(1)).to_contain_text('interactive blueprint')
    expect(page.locator('.approach-grid article').nth(2)).to_contain_text('local Lean source')
    assert 'Lean blueprints' in page.locator('meta[name="description"]').get_attribute('content')
    assert '中文介绍' not in (ROOT / 'README.md').read_text(encoding='utf-8')
    page.screenshot(path=str(ARTIFACTS / 'desktop-en.png'), full_page=True)

    for node in ['estimates', 'certificate', 'rounding', 'unions', 'comparison', 'convexity']:
        page.locator(f'[data-node="{node}"]').click()
        expect(page.locator(f'[data-node="{node}"]')).to_have_attribute('aria-pressed', 'true')
        assert 'github.com' in page.locator('#detail-source').get_attribute('href')
    page.locator('[data-mode="formal"]').click()
    expect(page.locator('#detail-code')).to_be_visible()
    expect(page.locator('#detail-code')).to_contain_text('discrete_convexity_theorem_1_1')
    page.locator('[data-mode="intuition"]').click()
    page.locator('[data-node="comparison"]').click()

    # Lean source opens locally, without creating a GitHub browser tab.
    pages_before = len(page.context.pages)
    page.locator('#detail-source').click()
    expect(page.locator('#lean-source-dialog')).to_be_visible()
    expect(page.locator('#lean-source-title')).to_have_text('Comparison.lean')
    expect(page.locator('.source-line.is-highlighted')).to_contain_text('comparison_theorem_1_1')
    assert len(page.context.pages) == pages_before
    assert page.locator('#source-github').get_attribute('href').endswith('Comparison.lean#L65')
    page.locator('#source-line-input').fill('1')
    page.locator('#source-go').click()
    expect(page.locator('.source-line.is-location')).to_have_attribute('data-line', '1')
    page.locator('#source-declaration').click()
    expect(page.locator('.source-line.is-location')).to_have_attribute('data-line', '65')
    expect(page.locator('.source-line.is-location')).to_be_in_viewport()
    page.context.grant_permissions(['clipboard-read', 'clipboard-write'])
    page.locator('#source-copy').click()
    expect(page.locator('#source-copy')).to_have_text('Copied')
    assert 'theorem comparison_theorem_1_1' in page.evaluate('navigator.clipboard.readText()')
    page.screenshot(path=str(ARTIFACTS / 'source-panel-en.png'))
    page.keyboard.press('Escape')
    expect(page.locator('#lean-source-dialog')).not_to_be_visible()

    # All collection indexes, scope views, search, and selectable prerequisites.
    for project in BLUEPRINT['projects']:
        page.locator('#bp-collection').select_option(project['id'])
        expect(page.locator('#bp-selected-name')).to_have_text(project['defaultNode'].split(':', 1)[1])
        page.locator('[data-bp-scope="all"]').click()
        expect(page.locator('.bp-node')).to_have_count(len(project['nodes']))
        page.locator('[data-bp-scope="ancestors"]').click()
        ancestors = page.locator('.bp-node').count()
        page.locator('[data-bp-scope="neighbors"]').click()
        assert ancestors >= 1
        reference = page.locator('[data-bp-reference]').first
        chosen = reference.get_attribute('data-bp-reference')
        reference.click()
        expect(page.locator('#bp-selected-name')).to_have_text(chosen.split(':', 1)[1])
        page.locator('#bp-home').click()
        expect(page.locator('#bp-selected-name')).to_have_text(project['defaultNode'].split(':', 1)[1])
        assert 'theorem ' in page.locator('#bp-statement').inner_text()
        assert page.locator('#bp-source').get_attribute('data-lean-line').isdigit()

    page.locator('#bp-collection').select_option('smallness')
    page.locator('#bp-search').fill('discrete_convexity_theorem_1_1')
    page.locator('#bp-search').press('ArrowDown')
    page.locator('#bp-search').press('Enter')
    expect(page.locator('#bp-selected-name')).to_have_text('TalagrandIntegral.discrete_convexity_theorem_1_1')
    expect(page.locator('.bp-explanation')).to_contain_text('From a large family to discrete convexity.')
    page.locator('#bp-search').fill('no-declaration-matches-this-xyz')
    expect(page.locator('.bp-search-empty')).to_be_visible()
    page.locator('#bp-search').press('Escape')
    expect(page.locator('#bp-search-menu')).not_to_be_visible()
    page.locator('#bp-search').fill('')
    page.locator('#bp-search').press('Escape')
    zoom_before = page.locator('#bp-zoom-value').inner_text()
    page.locator('#bp-zoom-in').click()
    assert page.locator('#bp-zoom-value').inner_text() != zoom_before
    page.locator('#bp-fit').click()
    assert page.locator('#bp-zoom-value').inner_text() == zoom_before
    box = page.locator('#bp-graph').bounding_box()
    transform_before = page.locator('#bp-scene').get_attribute('transform')
    page.mouse.move(box['x'] + 25, box['y'] + 25)
    page.mouse.down()
    page.mouse.move(box['x'] + 75, box['y'] + 65, steps=5)
    page.mouse.up()
    assert page.locator('#bp-scene').get_attribute('transform') != transform_before
    page.mouse.wheel(0, -100)
    expect(page.locator('#bp-zoom-value')).not_to_have_text(zoom_before)
    page.locator('#bp-fit').click()
    page.locator('#bp-graph').focus()
    transform_before = page.locator('#bp-scene').get_attribute('transform')
    page.keyboard.press('ArrowRight')
    assert transform_before != page.locator('#bp-scene').get_attribute('transform')
    page.keyboard.press('0')
    node = page.locator('.bp-node[aria-pressed="false"]').first
    chosen = node.get_attribute('data-bp-node')
    node.focus()
    page.keyboard.press('Enter')
    expect(page.locator('#bp-selected-name')).to_have_text(chosen.split(':', 1)[1])
    page.locator('#bp-home').click()
    page.locator('#bp-source').click()
    expect(page.locator('#lean-source-dialog')).to_be_visible()
    expect(page.locator('.source-line.is-highlighted').first).to_contain_text('comparison_theorem_1_1')
    page.keyboard.press('Escape')
    page.locator('#blueprint').screenshot(path=str(ARTIFACTS / 'blueprint-en.png'))

    page.locator('[data-filter="thresholds"]').click()
    expect(page.locator('.result-card')).to_have_count(2)
    page.locator('[data-filter="convexity"]').click()
    expect(page.locator('.result-card')).to_have_count(2)
    page.locator('[data-filter="all"]').click()
    page.locator('#search').fill('Kahn')
    expect(page.locator('.result-card')).to_have_count(1)
    page.locator('#search').fill('no such theorem xyz')
    expect(page.locator('#empty-state')).to_be_visible()
    page.locator('#search').fill('')

    for result in ['kahn-kalai', 'selector', 'five', 'smallness']:
        page.locator(f'[data-result="{result}"]').click()
        expect(page.locator('#result-dialog')).to_be_visible()
        expect(page.locator('.bibliography')).to_be_visible()
        assert page.locator('.bibliography li').count() >= 2
        if result == 'smallness':
            expect(page.locator('#dialog-content')).to_contain_text('OpenAI')
            assert page.locator('.bibliography a[href*="github.com/openai/math"]').count() >= 3
        page.keyboard.press('Escape')
        expect(page.locator('#result-dialog')).not_to_be_visible()

    for value, expected in [('0', '0.0%'), ('50', '63.7%'), ('100', '100.0%')]:
        page.locator('#probability').fill(value)
        expect(page.locator('#exact-value')).to_have_text(expected)
    page.locator('#probability').fill('35')
    page.locator('#reroll').click()
    expect(page.locator('.sample')).to_have_count(12)
    expect(page.locator('.sample-dot')).to_have_count(96)

    page.locator('[data-language="zh"]').click()
    expect(page.locator('html')).to_have_attribute('lang', 'zh-CN')
    expect(page.locator('#hero-title')).to_contain_text('看见数学的思路。')
    expect(page.locator('#about-heading')).to_have_text('从想法到可验证命题，走一条清晰的路。')
    expect(page.locator('.approach-grid article').nth(0)).to_contain_text('四个形式化成果集之一')
    expect(page.locator('.approach-grid article').nth(1)).to_contain_text('交互式证明蓝图')
    expect(page.locator('.approach-grid article').nth(2)).to_contain_text('本地 Lean 源码')
    expect(page.locator('[data-bp-scope="neighbors"]')).to_have_text('相邻节点')
    page.locator('#bp-source').click()
    expect(page.locator('#source-declaration')).to_have_text('当前声明')
    expect(page.locator('#source-copy')).to_have_text('复制文件')
    page.keyboard.press('Escape')
    page.reload(wait_until='networkidle')
    expect(page.locator('html')).to_have_attribute('lang', 'zh-CN')
    expect(page.locator('.result-card')).to_have_count(4)
    page.screenshot(path=str(ARTIFACTS / 'desktop-zh.png'), full_page=True)

    for language in ['zh', 'en']:
        page.locator(f'[data-language="{language}"]').click()
        for width in [320, 390, 768]:
            page.set_viewport_size({'width': width, 'height': 844})
            page.wait_for_timeout(100)
            assert page.evaluate('document.documentElement.scrollWidth <= window.innerWidth'), (language, width, 'horizontal overflow')
        page.set_viewport_size({'width': 390, 'height': 844})
        page.screenshot(path=str(ARTIFACTS / f'mobile-{language}.png'), full_page=True)
        page.locator('#bp-source').click()
        expect(page.locator('#lean-source-dialog')).to_be_visible()
        assert page.evaluate('document.documentElement.scrollWidth <= window.innerWidth'), (language, 'source panel overflow')
        page.screenshot(path=str(ARTIFACTS / f'source-panel-mobile-{language}.png'))
        page.keyboard.press('Escape')

    assert not errors, errors
    browser.close()
    print('PASS: both languages, persistence, curated graph, four blueprint indexes and scopes, declaration search and keyboard navigation, zoom, in-page Lean source, line navigation and copying, dialogs, bibliography, filters, exact probability, sampling, and mobile overflow. No JavaScript errors.')
