"""Read public bibliography records; run manually when updating site citations."""
import concurrent.futures
import html
import json
import re
from html.parser import HTMLParser
from pathlib import Path
import requests


class Metadata(HTMLParser):
    def __init__(self):
        super().__init__()
        self.meta = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        name = attrs.get('name', '')
        if tag == 'meta' and name.startswith('citation_'):
            self.meta.setdefault(name, []).append(attrs.get('content'))


urls = [
    'https://openai.com/index/sharing-ai-progress-in-mathematics/',
    'https://raw.githubusercontent.com/openai/math/main/preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/README.md',
    'https://raw.githubusercontent.com/openai/math/main/preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/README.md',
    'https://raw.githubusercontent.com/openai/math/main/lean/docs/175.md',
    'https://arxiv.org/abs/2203.17207v2',
    'https://arxiv.org/abs/2204.10309v2',
    'https://arxiv.org/abs/2212.14636v3',
    'https://arxiv.org/abs/2609.08967v1',
    'https://arxiv.org/abs/2609.18458v1',
    'https://arxiv.org/abs/2609.33644v1',
    'https://api.crossref.org/works/10.1090/jams/1028',
    'https://api.crossref.org/works/10.4007/annals.2024.199.3.6',
    'https://api.crossref.org/works/10.37236/12266',
    'https://api.crossref.org/works?query.title=Are%20many%20small%20sets%20explicitly%20small&rows=1',
    'https://api.crossref.org/works?query.title=Thresholds%20and%20expectation%20thresholds&rows=1',
]


def fetch(url):
    try:
        response = requests.get(url, timeout=35)
        response.raise_for_status()
        if 'crossref.org' in url:
            record = response.json()['message']
            if 'items' in record:
                record = record['items'][0]
            fields = ['title', 'author', 'container-title', 'published', 'published-print', 'volume', 'issue', 'page', 'DOI']
            result = {key: record[key] for key in fields if key in record}
        elif 'raw.githubusercontent.com' in url:
            result = {'text': response.text}
        elif 'openai.com' in url:
            body = re.sub(r'<script[\s\S]*?</script>|<style[\s\S]*?</style>', '', response.text)
            links = re.findall(r'href="([^" ]+)"', response.text)
            result = {'text': html.unescape(re.sub(r'\s+', ' ', re.sub('<[^>]+>', ' ', body)))[:16000], 'links': [html.unescape(link) for link in links if 'github.com/openai/math' in link]}
        else:
            parser = Metadata()
            parser.feed(response.text)
            result = parser.meta
            for field in ['jref', 'comments', 'abstract']:
                match = re.search(r'(?:class="[^"]*' + field + r'[^"]*">)(.*?)(?:</td>|</blockquote>)', response.text, re.S)
                if match:
                    result[field] = html.unescape(re.sub(r'\s+', ' ', re.sub('<[^>]+>', ' ', match[1]))).strip()
        return {'url': url, 'metadata': result}
    except Exception as error:
        return {'url': url, 'error': str(error)}


if __name__ == '__main__':
    records = list(concurrent.futures.ThreadPoolExecutor(6).map(fetch, urls))
    output = Path(__file__).resolve().parents[1] / 'web' / 'bibliography-records.json'
    output.write_text(json.dumps({'checked_on': '2026-10-09', 'records': records}, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps([{'url': record['url'], 'ok': 'metadata' in record, 'error': record.get('error')} for record in records], ensure_ascii=True, indent=2))
